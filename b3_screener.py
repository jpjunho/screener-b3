#!/usr/bin/env python3
"""
Screener de qualidade para ações da B3, com dados oficiais.

Fontes (públicas e gratuitas, baixadas como arquivos inteiros, sem raspar sites)
- B3, séries históricas de cotações (COTAHIST mensal): preço e volume
  financeiro de cada ticker nos últimos pregões.
- CVM, Formulário Cadastral (FCA): CNPJ de cada ticker, nome, setor e site de RI.
- CVM, DFP (anual) e ITR (trimestral): balanço, DRE, DVA e composição do
  capital. Usa as demonstrações consolidadas; a individual só entra quando a
  empresa não publica consolidado.

Por que não um site agregador: comparado com a CVM, o Dados de Mercado mostra
balanço individual (não consolidado) para a maioria dos bancos e calcula o
valor de mercado como "preço do ticker × total de ações", o que infla units e
distorce empresas com classes de preços diferentes.

Etapas
1. Cotações dos últimos pregões e filtro de liquidez (volume financeiro médio).
2. Ticker -> CNPJ pelo cadastro da CVM; classes da mesma empresa ficam juntas.
3. Demonstrações dos últimos exercícios e do último trimestre: histórico anual e
   valores dos últimos 12 meses (exercício anterior + acumulado do ano − mesmo
   período do ano anterior).
4. Valor de mercado = soma, por classe, de preço × ações em circulação.
5. Critérios, valuation e um HTML interativo e autocontido.

Critérios para empresas não financeiras (últimos 5 exercícios)
1. ROE > 15%
2. Margem líquida > 15%
3. Dívida líquida / EBITDA < 3x (últimos 12 meses)
4. Receita crescente: sem queda ano a ano e crescimento real ≥ 0 no período
5. Lucro crescente: idem

Bancos: as mesmas ideias, com a métrica que funciona para banco
1. ROE > 15%
2. ROA > 1% (no lugar da margem: quanto do ativo vira lucro)
3. Índice de Basileia ≥ 13% (no lugar da dívida; dado do IF.data do Banco Central)
4. Resultado bruto da intermediação crescente (no lugar da receita)
5. Lucro crescente

Seguradoras e holdings de participações (BB Seguridade, Itaúsa) vivem do lucro
das investidas: só ROE e lucro crescente são comparáveis.

Resultado
- Aprovada: atende todos os critérios à risca.
- Na margem: atende, mas usando a tolerância em algum critério: alguns anos
  de ROE ou margem entre 10% e 15%, ou quedas de até 10% na receita ou no
  lucro. Com n anos, até (n - 1) // 2 anos podem usar a tolerância: 1 com 3 ou
  4 anos, 2 com 5 anos.
- Falta 1: reprova em exatamente um critério.

"Crescente" tem duas partes: nenhuma queda de um ano para o outro (em valores
nominais, com a tolerância acima) e crescimento médio no período acima da
inflação (IPCA, do Banco Central). Dívida líquida / patrimônio aparece só como
informação.

Uso
    python b3_screener.py
    python b3_screener.py --tickers WEGE3 ITUB4 --output teste.html
    python b3_screener.py --min-volume 1000000 --refresh

A primeira execução baixa cerca de 110 MB (CVM e B3). Os arquivos ficam em
cache; as seguintes levam segundos.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import math
import re
import sys
import time
import zipfile
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Callable, Iterator, Optional
from urllib.parse import quote as url_quote

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

CVM_URL = "https://dados.cvm.gov.br/dados/CIA_ABERTA/DOC/{doc}/DADOS/{prefix}_cia_aberta_{year}.zip"
# IPCA mensal (%), série 433 do Sistema Gerenciador de Séries do Banco Central.
IPCA_URL = "https://api.bcb.gov.br/dados/serie/bcdata.sgs.433/dados?formato=json&dataInicial=01/01/{start}&dataFinal=31/12/{end}"
# IF.data do Banco Central: índice de Basileia dos conglomerados (relatório 5) e cadastro.
IFDATA_URL = "https://olinda.bcb.gov.br/olinda/servico/IFDATA/versao/v1/odata/"
COTAHIST_URL = "https://bvmf.bmfbovespa.com.br/InstDados/SerHist/COTAHIST_M{month:02d}{year}.ZIP"

DEFAULT_OUTPUT = Path("b3_screener.html")
DEFAULT_CACHE_DIR = Path(".b3_cache")
DEFAULT_CACHE_HOURS = 24.0
DEFAULT_MIN_VOLUME_BRL = 100_000.0
DEFAULT_SESSIONS = 20

MAX_HISTORY_YEARS = 5
MIN_HISTORY_YEARS = 3

ROE_MIN, ROE_TOLERATED = 0.15, 0.10
MARGIN_MIN, MARGIN_TOLERATED = 0.15, 0.10
MAX_DROP_PCT = 0.10
MAX_NET_DEBT_EBITDA = 3.0
ROA_MIN, ROA_TOLERATED = 0.01, 0.005
# Índice de Basileia: o mínimo regulatório com o colchão de conservação é
# 10,5%; os grandes bancos ficam entre 14% e 17%. 13% exige folga sobre o
# mínimo, como dívida < 3x EBITDA exige folga das empresas comuns.
BASEL_MIN = 0.13

REQUEST_TIMEOUT = 120
USER_AGENT = "b3-screener/2.0 (python-requests)"

NAO_FINANCEIRA = "nao_financeira"
BANCO = "banco"
SEGURADORA = "seguradora"
FINANCEIRA = "financeira"  # financeiras que não são bancos (crédito, leasing): avaliadas como bancos
HOLDING = "holding"  # holdings de participações financeiras (Itaúsa)


# ------------------------------------------------------------
# Download com cache
# ------------------------------------------------------------

def build_session() -> requests.Session:
    session = requests.Session()
    retry = Retry(
        total=4,
        backoff_factor=2.0,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=frozenset(["GET"]),
        respect_retry_after_header=True,
        raise_on_status=False,
    )
    session.mount("https://", HTTPAdapter(max_retries=retry))
    session.headers.update({"User-Agent": USER_AGENT})
    return session


class Downloader:
    """Baixa arquivos inteiros para o cache, reaproveitando os recentes.

    Arquivos de períodos encerrados (cotações de meses passados) não mudam e
    nunca são baixados de novo. Se a rede falhar e houver cópia antiga, usa a
    cópia e registra um aviso.
    """

    def __init__(self, directory: Path, max_age_hours: float, refresh: bool):
        self.directory = directory
        self.max_age_seconds = max_age_hours * 3600
        self.refresh = refresh
        self.session = build_session()
        self.warnings: list[str] = []
        directory.mkdir(parents=True, exist_ok=True)

    def get(self, url: str, final_after: Optional[datetime] = None, name: Optional[str] = None) -> Optional[Path]:
        """Retorna o caminho local, ou None se o arquivo não existe na origem.

        final_after: a partir desse momento o conteúdo não muda mais; uma cópia
        baixada depois disso vale para sempre.
        name: nome do arquivo no cache (padrão: o final da URL).
        """
        path = self.directory / (name or url.rsplit("/", 1)[1])
        if path.exists() and not self.refresh:
            mtime = path.stat().st_mtime
            if final_after is not None and mtime > final_after.timestamp():
                return path
            if time.time() - mtime < self.max_age_seconds:
                return path
        print(f"  baixando {url}", flush=True)
        try:
            response = self.session.get(url, timeout=REQUEST_TIMEOUT, stream=True)
            if response.status_code == 404:
                return None
            response.raise_for_status()
            partial = path.with_suffix(path.suffix + ".part")
            with partial.open("wb") as fh:
                for chunk in response.iter_content(chunk_size=1 << 20):
                    fh.write(chunk)
            partial.replace(path)
            return path
        except requests.RequestException as exc:
            if path.exists():
                self.warnings.append(f"Falha ao atualizar {path.name} ({type(exc).__name__}); usada a cópia do cache.")
                return path
            raise


# ------------------------------------------------------------
# Utilidades
# ------------------------------------------------------------

def normalize_spaces(text: object) -> str:
    return re.sub(r"\s+", " ", str(text or "")).strip()


def normalize_label(text: object) -> str:
    return normalize_spaces(text).casefold()


def safe_div(numerator: Optional[float], denominator: Optional[float]) -> Optional[float]:
    if numerator is None or not denominator:
        return None
    return numerator / denominator


def fmt_pct(value: Optional[float]) -> str:
    return "—" if value is None else f"{value * 100:.1f}%".replace(".", ",").replace(",0%", "%")


def fmt_num(value: float, digits: int = 2) -> str:
    """1234.5 -> '1.234,50' (separadores brasileiros)."""
    return f"{value:,.{digits}f}".replace(",", "\0").replace(".", ",").replace("\0", ".")


def fmt_bi(value: float) -> str:
    return f"R$ {fmt_num(value / 1e9)} bi"


def fmt_mult(value: Optional[float]) -> str:
    return "—" if value is None else f"{value:.2f}x".replace(".", ",")


def plural(n: int, singular: str, plural_form: str) -> str:
    return f"{n} {singular if n == 1 else plural_form}"


def shift_year(iso_date: str, years: int) -> str:
    d = date.fromisoformat(iso_date)
    try:
        return d.replace(year=d.year + years).isoformat()
    except ValueError:  # 29 de fevereiro
        return d.replace(year=d.year + years, day=28).isoformat()


def day_before(iso_date: str) -> str:
    return (date.fromisoformat(iso_date) - timedelta(days=1)).isoformat()


def pretty_name(raw: str) -> str:
    """'ITAU UNIBANCO HOLDING S.A.' -> 'Itau Unibanco Holding S.A.'."""
    small = {"de", "da", "do", "das", "dos", "e"}
    words = []
    for i, word in enumerate(normalize_spaces(raw).split(" ")):
        lower = word.lower()
        if lower in {"s.a.", "s.a", "s/a", "sa"}:
            words.append("S.A.")
        elif i and lower in small:
            words.append(lower)
        elif len(word) <= 3 and word.isalpha() and not re.search(r"[aeiouáéíóú]", lower):
            words.append(word.upper())  # siglas como BRF, CPFL não ficam "Brf"
        else:
            words.append(word[:1].upper() + word[1:].lower())
    return " ".join(words)


# ------------------------------------------------------------
# Cotações (B3)
# ------------------------------------------------------------

@dataclass
class Quote:
    ticker: str
    classe: str  # ON, PN ou UNT
    preco: float
    data: str
    volume_medio: float  # R$ por pregão, média dos últimos pregões (0 nos dias sem negócio)


def load_quotes(dl: Downloader, sessions: int, today: date) -> tuple[dict[str, Quote], str]:
    """Lê os arquivos COTAHIST mensais: mercado à vista, lote padrão, ações e units."""
    months = []
    y, m = today.year, today.month
    for _ in range(3):
        months.append((y, m))
        y, m = (y, m - 1) if m > 1 else (y - 1, 12)

    daily: dict[str, dict[str, tuple[float, float]]] = {}
    classes: dict[str, str] = {}
    for year, month in reversed(months):
        next_month = date(year + (month == 12), month % 12 + 1, 1)
        path = dl.get(COTAHIST_URL.format(month=month, year=year),
                      final_after=datetime.combine(next_month + timedelta(days=1), datetime.min.time()))
        if path is None:
            continue  # mês corrente sem pregão ainda
        with zipfile.ZipFile(path) as zf, zf.open(zf.namelist()[0]) as fh:
            for raw in fh:
                line = raw.decode("latin-1")
                # registro 01, BDI 02 (lote padrão), mercado 010 (à vista)
                if line[:2] != "01" or line[10:12] != "02" or line[24:27] != "010":
                    continue
                especie = line[39:49].split()
                kind = especie[0] if especie else ""
                classe = "ON" if kind == "ON" else "PN" if kind.startswith("PN") else "UNT" if kind == "UNT" else None
                if classe is None:
                    continue
                ticker = line[12:24].strip()
                day = f"{line[2:6]}-{line[6:8]}-{line[8:10]}"
                daily.setdefault(ticker, {})[day] = (int(line[108:121]) / 100, int(line[170:188]) / 100)
                classes[ticker] = classe

    all_days = sorted({d for days in daily.values() for d in days})
    if not all_days:
        raise RuntimeError("Não encontrei cotações nos arquivos da B3.")
    window = all_days[-sessions:]
    quotes = {}
    for ticker, days in daily.items():
        last_day = max(days)
        volume = sum(days[d][1] for d in window if d in days) / len(window)
        quotes[ticker] = Quote(ticker, classes[ticker], days[last_day][0], last_day, volume)
    return quotes, all_days[-1]


# ------------------------------------------------------------
# Inflação (Banco Central)
# ------------------------------------------------------------

def load_ipca(dl: Downloader, today: date) -> dict[str, float]:
    """IPCA de cada ano completo, como fração (2025 -> 0.043)."""
    start = today.year - MAX_HISTORY_YEARS - 1
    path = dl.get(IPCA_URL.format(start=start, end=today.year), name="ipca_433.json")
    if path is None:
        return {}
    monthly: dict[str, list[float]] = {}
    for item in json.loads(path.read_text(encoding="utf-8")):
        day, month, year = item["data"].split("/")
        monthly.setdefault(year, []).append(float(item["valor"]))
    return {year: math.prod(1 + v / 100 for v in values) - 1
            for year, values in monthly.items() if len(values) == 12}


def load_basel(dl: Downloader, today: date) -> tuple[dict[str, float], Optional[str]]:
    """Índice de Basileia por raiz do CNPJ (8 dígitos) do líder de cada
    conglomerado prudencial, no trimestre mais recente publicado (o Banco
    Central divulga com uns 3 meses de atraso). Devolve (índices, 'AAAAMM')."""
    quarters = []
    year, month = today.year, today.month - (today.month - 1) % 3 + 2  # fim do trimestre corrente
    for _ in range(6):
        quarters.append(f"{year}{month:02d}")
        year, month = (year, month - 3) if month > 3 else (year - 1, 12)
    basel_filter = url_quote("startswith(NomeColuna,'Índice de Basileia')")
    for anomes in quarters:
        if date(int(anomes[:4]), int(anomes[4:]), 1) > today:
            continue
        values_url = (f"{IFDATA_URL}IfDataValores(AnoMes=@AnoMes,TipoInstituicao=@TipoInstituicao,Relatorio=@Relatorio)"
                      f"?@AnoMes={anomes}&@TipoInstituicao=1&@Relatorio='5'&$filter={basel_filter}&$format=json")
        path = dl.get(values_url, name=f"ifdata_basileia_{anomes}.json")
        values = json.loads(path.read_text(encoding="utf-8"))["value"] if path else []
        by_code = {v["CodInst"]: v["Saldo"] for v in values if v.get("Saldo") is not None}
        if not by_code:
            continue
        path = dl.get(f"{IFDATA_URL}IfDataCadastro(AnoMes=@AnoMes)?@AnoMes={anomes}&$format=json",
                      name=f"ifdata_cadastro_{anomes}.json")
        registry = json.loads(path.read_text(encoding="utf-8"))["value"] if path else []
        basel: dict[str, float] = {}
        for inst in registry:
            root, group = inst.get("CnpjInstituicaoLider"), inst.get("CodConglomeradoPrudencial")
            if root and group in by_code:
                basel.setdefault(root, by_code[group])
        for code, value in by_code.items():  # instituições independentes usam a raiz do CNPJ como código
            if code.isdigit() and len(code) == 8:
                basel.setdefault(code, value)
        return basel, anomes
    return {}, None


def cnpj_root(cnpj: str) -> str:
    return re.sub(r"\D", "", cnpj)[:8]


# ------------------------------------------------------------
# Cadastro (CVM FCA)
# ------------------------------------------------------------

@dataclass
class Company:
    cnpj: str
    nome: str
    setor: str
    site_ri: Optional[str] = None


def iter_csv(zip_path: Path, member: str, cnpjs: Optional[set[str]] = None) -> Iterator[dict[str, str]]:
    """Linhas de um CSV da CVM (latin-1, ';'). Filtrar pelo CNPJ (primeira
    coluna, 18 caracteres) antes do parse deixa a leitura bem mais rápida."""
    with zipfile.ZipFile(zip_path) as zf:
        if member not in zf.namelist():
            return
        with zf.open(member) as fh:
            text = io.TextIOWrapper(fh, encoding="latin-1", newline="")
            header = next(csv.reader([text.readline()], delimiter=";"))
            lines: Iterator[str] = text if cnpjs is None else (ln for ln in text if ln[:18] in cnpjs)
            for row in csv.reader(lines, delimiter=";"):
                yield dict(zip(header, row))


def unit_size(composition: str) -> Optional[int]:
    """'1 ON / 2 PN' -> 3; '1 KLBN3 + 4 KLBN4' -> 5 (ignora os números dos tickers)."""
    numbers = [int(n) for n in re.findall(r"\d+", re.sub(r"\b[A-Z]{4}\d{1,2}\b", "", composition.upper()))]
    return sum(numbers) or None


def load_registry(dl: Downloader, year: int) -> tuple[dict[str, str], dict[str, Company], dict[str, int]]:
    """Ticker -> CNPJ, dados da empresa e quantas ações compõem cada unit. Usa
    o FCA do ano e do anterior, porque nem toda empresa reenvia o formulário
    todo ano."""
    by_ticker: dict[str, str] = {}
    companies: dict[str, Company] = {}
    unit_sizes: dict[str, int] = {}
    for y in (year - 1, year):  # o mais novo sobrescreve
        path = dl.get(CVM_URL.format(doc="FCA", prefix="fca", year=y))
        if path is None:
            continue
        for row in iter_csv(path, f"fca_cia_aberta_geral_{y}.csv"):
            site = row.get("Pagina_Web") or None
            if site and not site.startswith("http"):
                site = "https://" + site
            companies[row["CNPJ_Companhia"]] = Company(
                row["CNPJ_Companhia"], pretty_name(row["Nome_Empresarial"]), row["Setor_Atividade"], site)
        for row in iter_csv(path, f"fca_cia_aberta_valor_mobiliario_{y}.csv"):
            code = row["Codigo_Negociacao"].strip().upper()
            if code and row["Valor_Mobiliario"] in {"Ações Ordinárias", "Ações Preferenciais", "Units"}:
                by_ticker[code] = row["CNPJ_Companhia"]
                size = unit_size(row.get("Composicao_BDR_Unit") or "") if row["Valor_Mobiliario"] == "Units" else None
                if size:
                    unit_sizes[code] = size
    return by_ticker, companies, unit_sizes


# Empresas cujo FCA não traz os códigos de negociação (conferido em nov/2026).
# Tickers líquidos que continuarem sem CNPJ aparecem nos avisos do relatório.
KNOWN_ROOTS = {
    "BPAC": "30.306.294/0001-45",  # Banco BTG Pactual
    "CSNA": "33.042.730/0001-04",  # Cia Siderúrgica Nacional
    "CMIN": "08.902.291/0001-15",  # CSN Mineração
    "MBRF": "03.853.896/0001-40",  # MBRF Global Foods (ex-Marfrig)
    "AMAR": "61.189.288/0001-89",  # Marisa Lojas
    "EQPA": "04.895.728/0001-80",  # Equatorial Pará
}


def resolve_cnpj(ticker: str, by_ticker: dict[str, str]) -> Optional[str]:
    """Pelo ticker exato, pelo radical (TAEE11 -> TAEE3/TAEE4) ou pela tabela acima."""
    if ticker in by_ticker:
        return by_ticker[ticker]
    same_root = {cnpj for t, cnpj in by_ticker.items() if t[:4] == ticker[:4]}
    if len(same_root) == 1:
        return same_root.pop()
    return KNOWN_ROOTS.get(ticker[:4])


# ------------------------------------------------------------
# Demonstrações financeiras (CVM DFP e ITR)
# ------------------------------------------------------------

@dataclass
class Balance:
    ativo: Optional[float] = None
    ativo_circ: Optional[float] = None
    passivo_circ: Optional[float] = None
    caixa: Optional[float] = None
    aplicacoes: Optional[float] = None
    divida: Optional[float] = None
    pl: Optional[float] = None
    pl_minor: Optional[float] = None
    recebiveis: Optional[float] = None
    estoques: Optional[float] = None

    @property
    def pl_ctrl(self) -> Optional[float]:
        return None if self.pl is None else self.pl - (self.pl_minor or 0.0)

    @property
    def divida_liquida(self) -> Optional[float]:
        if self.divida is None or self.caixa is None:
            return None
        return self.divida - self.caixa - (self.aplicacoes or 0.0)


@dataclass
class Flow:
    receita: Optional[float] = None
    receita_desc: str = ""
    ebit: Optional[float] = None
    lucro: Optional[float] = None
    lucro_ctrl: Optional[float] = None
    da: Optional[float] = None
    lpa: Optional[float] = None
    # Para os sinais de qualidade do lucro.
    lair: Optional[float] = None  # lucro antes dos tributos
    ir: Optional[float] = None  # IR e CSLL (negativo = despesa)
    ir_diferido: Optional[float] = None
    outras_operacionais: Optional[float] = None  # outras receitas − outras despesas operacionais
    equivalencia: Optional[float] = None
    descontinuadas: Optional[float] = None
    fco: Optional[float] = None  # caixa líquido das atividades operacionais
    intermediacao: Optional[float] = None  # bancos: resultado bruto da intermediação financeira

    @property
    def ebitda(self) -> Optional[float]:
        if self.ebit is None or self.da is None:
            return None
        return self.ebit + abs(self.da)


@dataclass
class Capital:
    dt_refer: str
    on: float  # em circulação (sem tesouraria), na escala informada pela empresa
    pn: float


@dataclass
class CompanyData:
    consolidado: bool = True
    balances: dict[str, Balance] = field(default_factory=dict)  # data -> balanço
    flows: dict[tuple[str, str], Flow] = field(default_factory=dict)  # (início, fim) -> resultado
    capital: Optional[Capital] = None
    ultimo_doc: Optional[tuple[str, str]] = None  # (data de referência, link)
    periodos_individuais: int = 0  # períodos em que o consolidado veio vazio e a individual completou
    reapresentadas: dict[str, int] = field(default_factory=dict)  # ano da DFP -> versão, quando > 1
    parecer: Optional[tuple[str, str, bool]] = None  # (ano, tipo do relatório, incerteza sobre continuidade)


Accounts = dict[str, tuple[str, float]]  # código -> (descrição, valor em R$)


def _account(acc: Accounts, depth: int, root: str, starts: str) -> Optional[tuple[str, float]]:
    """Primeira conta do nível `depth` sob `root` cuja descrição começa com `starts`."""
    for code in sorted(acc):
        desc, value = acc[code]
        if code.startswith(root + ".") and code.count(".") == depth and normalize_label(desc).startswith(starts):
            return code, value
    return None


def _children(acc: Accounts, parent: str) -> Iterator[tuple[str, str, float]]:
    depth = parent.count(".") + 1
    for code, (desc, value) in acc.items():
        if code.startswith(parent + ".") and code.count(".") == depth:
            yield code, normalize_label(desc), value


def extract_balance(acc: Accounts) -> Balance:
    b = Balance()
    if "1" in acc:
        b.ativo = acc["1"][1]
    circ = _account(acc, 1, "1", "ativo circulante")
    if circ:
        b.ativo_circ = circ[1]
        for _, desc, value in _children(acc, circ[0]):
            if desc.startswith("caixa e equivalentes"):
                b.caixa = value
            elif desc.startswith("aplicações financeiras"):
                b.aplicacoes = value
            elif desc.startswith("contas a receber"):
                b.recebiveis = value
            elif desc.startswith("estoques"):
                b.estoques = value
    passivo_circ = _account(acc, 1, "2", "passivo circulante")
    passivo_nc = _account(acc, 1, "2", "passivo não circulante")
    if passivo_circ:
        b.passivo_circ = passivo_circ[1]
    loans = [value for parent in (passivo_circ, passivo_nc) if parent
             for _, desc, value in _children(acc, parent[0]) if desc.startswith("empréstimos e financiamentos")]
    if loans:
        b.divida = sum(loans)
    pl = _account(acc, 1, "2", "patrimônio líquido")
    if pl:
        b.pl = pl[1]
        b.pl_minor = next((v for _, d, v in _children(acc, pl[0]) if "não controladores" in d), 0.0)
    return b


def extract_flow(acc: Accounts) -> Flow:
    f = Flow()
    if "3.01" in acc:
        f.receita_desc, f.receita = acc["3.01"]
    ebit = _account(acc, 1, "3", "resultado antes do resultado financeiro")
    if ebit:
        f.ebit = ebit[1]
    # Lucro líquido: a última conta de nível 1 "lucro ... do período/exercício".
    # O rótulo varia: "Lucro/Prejuízo Consolidado do Período" (empresas),
    # "Lucro ou Prejuízo Líquido Consolidado do Período" (BB, Bradesco).
    net = [(code, value) for code, (desc, value) in sorted(acc.items())
           if code.startswith("3.") and code.count(".") == 1 and code != "3.99"
           and "lucro" in (d := normalize_label(desc)) and ("período" in d or "exercício" in d) and "antes" not in d]
    if net:
        code, f.lucro = net[-1]
        # Muitas empresas deixam "atribuído à controladora" zerado e só informam
        # o total; nesse caso, controladora = total − não controladores. Na
        # demonstração individual não há essa divisão: o total já é da controladora.
        children = list(_children(acc, code))
        ctrl = next((v for _, d, v in children if "controladora" in d), 0.0)
        minority = next((v for _, d, v in children if "não controladores" in d), 0.0)
        f.lucro_ctrl = ctrl if ctrl else f.lucro - minority
    # LPA básico da ação ON; algumas empresas só preenchem o nível de cima.
    for code in ("3.99.01.01", "3.99.01", "3.99"):
        if acc.get(code, ("", 0.0))[1]:
            f.lpa = acc[code][1]
            break
    for code, (desc, value) in acc.items():
        if code.startswith("7.") and normalize_label(desc).startswith("depreciação, amortização e exaustão"):
            f.da = value
            break

    lair = _account(acc, 1, "3", "resultado antes dos tributos")
    if lair:
        f.lair = lair[1]
    ir = _account(acc, 1, "3", "imposto de renda e contribuição social")
    if ir:
        f.ir = ir[1]
        f.ir_diferido = next((v for _, d, v in _children(acc, ir[0]) if d.startswith("diferido")), None)
    f.descontinuadas = next((value for code, (desc, value) in sorted(acc.items())
                             if code.startswith("3.") and code.count(".") == 1
                             and "operações descontinuadas" in normalize_label(desc)), None)
    operating = _account(acc, 1, "3", "despesas/receitas operacionais")
    if operating:
        children = list(_children(acc, operating[0]))
        others = [v for _, d, v in children if d.startswith(("outras receitas operacionais", "outras despesas operacionais"))]
        f.outras_operacionais = sum(others) if others else None
        f.equivalencia = next((v for _, d, v in children if d.startswith("resultado de equivalência")), None)
    if "6.01" in acc:
        f.fco = acc["6.01"][1]
    # Juros recebidos − custo de captação − provisões para perdas: o "lucro bruto" de um banco.
    f.intermediacao = next((value for code, (desc, value) in sorted(acc.items())
                            if code.startswith("3.") and code.count(".") == 1
                            and normalize_label(desc).startswith("resultado bruto")
                            and "intermediação" in normalize_label(desc)), None)
    return f


STATEMENTS = ("BPA", "BPP", "DRE", "DVA", "DFC_MI", "DFC_MD")


def _keep_account(code: str) -> bool:
    return code.count(".") <= 2 or code == "3.99.01.01"


def load_fundamentals(dl: Downloader, cnpjs: set[str], today: date) -> dict[str, CompanyData]:
    """Lê DFPs dos últimos anos e o ITR do ano corrente.

    Documentos são aplicados do mais antigo para o mais novo, então valores
    reapresentados (coluna do ano anterior num documento mais novo) prevalecem.
    Consolidado tem prioridade; a individual entra nos períodos em que o
    consolidado não existe ou veio zerado.
    """
    sources: list[tuple[str, int, Path]] = []
    first_year = today.year - (MAX_HISTORY_YEARS - 1)
    for year in range(first_year, today.year + 1):
        for doc in ("DFP", "ITR"):
            if doc == "ITR" and year != today.year:
                continue  # ITRs de anos encerrados não acrescentam nada aos DFPs
            path = dl.get(CVM_URL.format(doc=doc, prefix=doc.lower(), year=year))
            if path is not None:
                sources.append((doc, year, path))

    data: dict[str, CompanyData] = {}
    from_consolidated: dict[str, set] = {}  # períodos que vieram do consolidado, por empresa
    for kind in ("con", "ind"):
        targets = cnpjs
        for doc, year, path in sources:
            prefix = f"{doc.lower()}_cia_aberta"
            # (cnpj, data de referência, versão) -> (início, fim) -> contas
            raw: dict[tuple[str, str, int], dict[tuple[str, str, str], Accounts]] = {}
            for stmt in STATEMENTS:
                for row in iter_csv(path, f"{prefix}_{stmt}_{kind}_{year}.csv", targets):
                    code = row["CD_CONTA"]
                    if not _keep_account(code):
                        continue
                    value = float(row["VL_CONTA"] or 0)
                    if not code.startswith("3.99") and row["ESCALA_MOEDA"] == "MIL":
                        value *= 1000
                    group = "balanco" if stmt in ("BPA", "BPP") else "resultado"
                    period = (group, row.get("DT_INI_EXERC", "") if group == "resultado" else "", row["DT_FIM_EXERC"])
                    doc_key = (row["CNPJ_CIA"], row["DT_REFER"], int(row["VERSAO"] or 1))
                    raw.setdefault(doc_key, {}).setdefault(period, {})[code] = (row["DS_CONTA"], value)

            latest_version: dict[tuple[str, str], int] = {}
            for cnpj, refer, version in raw:
                latest_version[(cnpj, refer)] = max(version, latest_version.get((cnpj, refer), 0))
            for (cnpj, refer, version), periods in sorted(raw.items(), key=lambda kv: (kv[0][1], kv[0][2])):
                if version != latest_version[(cnpj, refer)]:
                    continue
                # Períodos do documento mais recente vêm por último e prevalecem.
                # Algumas empresas entregam o consolidado todo zerado (TIM) ou
                # zerado em anos sem controladas (Sabesp em 2022): período vazio
                # no consolidado é ignorado e a individual preenche a lacuna.
                consolidated_keys = from_consolidated.setdefault(cnpj, set())
                for (group, start, end), acc in sorted(periods.items(), key=lambda kv: kv[0][2]):
                    key = (group, start, end)
                    extracted = extract_balance(acc) if group == "balanco" else extract_flow(acc)
                    empty = not extracted.ativo if group == "balanco" else not (extracted.receita or extracted.lucro or extracted.ebit)
                    if empty or (kind == "ind" and key in consolidated_keys):
                        continue
                    company = data.setdefault(cnpj, CompanyData(consolidado=kind == "con"))
                    if kind == "con":
                        consolidated_keys.add(key)
                    elif company.consolidado:
                        company.periodos_individuais += 1
                    if group == "balanco":
                        company.balances[end] = extracted  # type: ignore[assignment]
                    else:
                        company.flows[(start, end)] = extracted  # type: ignore[assignment]

    # Composição do capital e link do documento mais recente de cada empresa.
    for doc, year, path in sources:
        prefix = f"{doc.lower()}_cia_aberta"
        for row in iter_csv(path, f"{prefix}_composicao_capital_{year}.csv", set(data)):
            company = data[row["CNPJ_CIA"]]
            if company.capital is None or row["DT_REFER"] >= company.capital.dt_refer:
                num = lambda key: float(row.get(key) or 0)  # noqa: E731
                company.capital = Capital(
                    row["DT_REFER"],
                    num("QT_ACAO_ORDIN_CAP_INTEGR") - num("QT_ACAO_ORDIN_TESOURO"),
                    num("QT_ACAO_PREF_CAP_INTEGR") - num("QT_ACAO_PREF_TESOURO"),
                )
        for row in iter_csv(path, f"{prefix}_{year}.csv", set(data)):
            company = data[row["CNPJ_CIA"]]
            if company.ultimo_doc is None or row["DT_REFER"] >= company.ultimo_doc[0]:
                company.ultimo_doc = (row["DT_REFER"], row.get("LINK_DOC", ""))
            version = int(row.get("VERSAO") or 1)
            if doc == "DFP" and version > 1:
                year_ref = row["DT_REFER"][:4]
                company.reapresentadas[year_ref] = max(version, company.reapresentadas.get(year_ref, 0))

    # Relatório do auditor da DFP mais recente. O texto ocupa várias linhas do
    # CSV (campos com quebra de linha), então aqui não dá para filtrar a linha
    # pelo CNPJ antes do parse.
    reports: dict[tuple[str, str], list] = {}
    for doc, year, path in sources:
        if doc != "DFP":
            continue
        for row in iter_csv(path, f"dfp_cia_aberta_parecer_{year}.csv"):
            if row["CNPJ_CIA"] in data and row["TP_PARECER_DECL"] == "Relatório do Auditor Independente":
                entry = reports.setdefault((row["CNPJ_CIA"], row["DT_REFER"]), [row["TP_RELAT_AUD"], ""])
                entry[1] += " " + row["TXT_PARECER_DECL"]
    for (cnpj, refer), (kind_of_report, text) in sorted(reports.items(), key=lambda kv: kv[0][1]):
        text = normalize_label(text)
        going_concern = any(f"incerteza {w} relacionada com a continuidade operacional" in text for w in ("relevante", "significativa"))
        data[cnpj].parecer = (refer[:4], kind_of_report or "Não informado", going_concern)
    return data


def annual_flows(data: CompanyData) -> dict[str, Flow]:
    """Exercícios completos (≈ 12 meses), indexados pelo ano de encerramento."""
    out: dict[str, tuple[str, Flow]] = {}
    for (start, end), flow in data.flows.items():
        if start and (date.fromisoformat(end) - date.fromisoformat(start)).days >= 360:
            year = end[:4]
            if year not in out or end > out[year][0]:
                out[year] = (end, flow)
    return {year: flow for year, (_, flow) in out.items()}


def annual_end_dates(data: CompanyData) -> dict[str, str]:
    ends: dict[str, str] = {}
    for (start, end) in data.flows:
        if start and (date.fromisoformat(end) - date.fromisoformat(start)).days >= 360:
            ends[end[:4]] = max(end, ends.get(end[:4], end))
    return ends


def trailing_twelve_months(data: CompanyData) -> tuple[Optional[Flow], Optional[str], bool]:
    """(resultado dos últimos 12 meses, data final, se é aproximação).

    Com ITR: exercício anterior + acumulado do ano − mesmo período do ano
    anterior. Se faltar alguma parte, usa o último exercício completo e marca
    como aproximação.
    """
    if not data.flows:
        return None, None, False
    latest_end = max(end for _, end in data.flows)
    ytd_start, ytd = min(((s, f) for (s, e), f in data.flows.items() if e == latest_end and s), default=(None, None))
    if ytd is None or ytd_start is None:
        return None, None, False
    if (date.fromisoformat(latest_end) - date.fromisoformat(ytd_start)).days >= 360:
        return ytd, latest_end, False
    prev_ytd = data.flows.get((shift_year(ytd_start, -1), shift_year(latest_end, -1)))
    prev_year = data.flows.get((shift_year(ytd_start, -1), day_before(ytd_start)))
    if prev_ytd is None or prev_year is None:
        annual = annual_flows(data)
        if not annual:
            return None, None, False
        year = max(annual)
        return annual[year], annual_end_dates(data)[year], True

    def combine(a: Optional[float], b: Optional[float], c: Optional[float]) -> Optional[float]:
        return None if a is None or b is None or c is None else a + b - c

    ttm = Flow(
        receita=combine(prev_year.receita, ytd.receita, prev_ytd.receita),
        receita_desc=ytd.receita_desc,
        ebit=combine(prev_year.ebit, ytd.ebit, prev_ytd.ebit),
        lucro=combine(prev_year.lucro, ytd.lucro, prev_ytd.lucro),
        lucro_ctrl=combine(prev_year.lucro_ctrl, ytd.lucro_ctrl, prev_ytd.lucro_ctrl),
        da=combine(prev_year.da, ytd.da, prev_ytd.da),
    )
    return ttm, latest_end, False


def shares_outstanding(
    data: CompanyData, price: Optional[float], equity: Optional[float],
) -> tuple[Optional[float], Optional[float], Optional[str]]:
    """(ações ON, ações PN, aviso se a contagem é duvidosa).

    A CVM não informa a unidade da composição do capital: umas empresas mandam
    em unidades, outras em milhares. A escala certa é a que bate com o número de
    ações implícito no lucro por ação (lucro ÷ LPA). Quando o LPA claramente
    não serve (erro de digitação, fora de 0,5x a 2x), a escala é a que deixa o
    P/VP plausível; as duas opções diferem 1.000x, então não há ambiguidade.

    Em ~15% das empresas pequenas as duas fontes divergem de verdade (contagem
    desatualizada após grupamento ou aumento de capital, ou LPA com erro). Não
    há terceira fonte oficial para desempatar, então o valuation sai com aviso.
    """
    cap = data.capital
    if cap is None or cap.on + cap.pn <= 0:
        return None, None, None
    total = cap.on + cap.pn
    implied = None
    for _, flow in sorted(data.flows.items(), key=lambda kv: kv[0][1], reverse=True):
        if flow.lpa and flow.lucro_ctrl:
            implied = abs(flow.lucro_ctrl / flow.lpa)
            break

    scale, ratio = None, None
    if implied:
        scale = min((1, 1000), key=lambda s: abs(math.log(total * s / implied)))
        ratio = total * scale / implied
        if not 0.5 <= ratio <= 2:
            scale = None
    if scale is None:
        if not (price and equity and equity > 0):
            return None, None, None
        scale = min((1, 1000), key=lambda s: abs(math.log(total * s * price / equity / 1.5)))
    warning = None
    if ratio is not None and not 0.8 <= ratio <= 1.25:
        warning = (f"Número de ações divergente na CVM: {fmt_num(total * scale / 1e6, 1)} milhões declaradas no capital "
                   f"× {fmt_num(implied / 1e6, 1)} milhões implícitas no lucro por ação. O valuation pode estar errado.")
    return cap.on * scale, cap.pn * scale, warning


def financial_profile(setor: str, receita_desc: str) -> str:
    """Perfil pelo setor do cadastro da CVM, com o layout da DRE como reforço
    (bancos publicam 'Receitas da Intermediação Financeira'). Holdings de
    participações financeiras (Itaúsa) vivem do lucro das investidas e ficam
    num perfil próprio."""
    full = normalize_label(setor)
    sector = full.removeprefix("emp. adm. part. - ")
    financial_sectors = {"intermediação financeira", "arrendamento mercantil", "crédito imobiliário", "securitização de recebíveis"}
    if sector == "bancos":
        return BANCO
    if sector == "seguradoras e corretoras":
        return SEGURADORA
    if sector in financial_sectors:
        return HOLDING if full.startswith("emp. adm. part.") else FINANCEIRA
    if "intermediação financeira" in normalize_label(receita_desc):
        return BANCO
    return NAO_FINANCEIRA


# ------------------------------------------------------------
# Regras
# ------------------------------------------------------------

def tolerance(n_years: int) -> int:
    """Anos fora da regra principal aceitos: 1 com 3 ou 4 anos, 2 com 5 anos."""
    return max(0, (n_years - 1) // 2)


# As avaliações históricas devolvem (passou, detalhe, passou só pela tolerância).
Evaluation = tuple[bool, str, bool]


def evaluate_threshold(years_desc: list[str], values_desc: list[float], minimum: float, tolerated: float) -> Evaluation:
    """Regra: todo ano acima de `minimum`. Tolerância: alguns anos entre
    `tolerated` e `minimum`."""
    n = len(values_desc)
    allowed = tolerance(n)
    lowest = min(range(n), key=values_desc.__getitem__)
    in_band = sum(1 for v in values_desc if tolerated <= v <= minimum)
    passed = values_desc[lowest] >= tolerated and in_band <= allowed
    detail = (
        f"{n} anos; menor valor {fmt_pct(values_desc[lowest])} em {years_desc[lowest]}; "
        f"{plural(in_band, 'ano', 'anos')} entre {fmt_pct(tolerated)} e {fmt_pct(minimum)} (tolera {allowed})"
    )
    return passed, detail, passed and in_band > 0


def evaluate_growth(years_desc: list[str], values_desc: list[float]) -> Evaluation:
    """Regra: nenhuma queda de um ano para o outro. Tolerância: algumas quedas
    pequenas."""
    years, values = years_desc[::-1], values_desc[::-1]
    drops = 0
    worst: Optional[tuple[float, str]] = None
    for i in range(1, len(values)):
        prev, curr = values[i - 1], values[i]
        if curr >= prev:
            continue
        drops += 1
        drop = (prev - curr) / prev if prev > 0 else math.inf  # prejuízo maior é sempre queda relevante
        if worst is None or drop > worst[0]:
            worst = (drop, years[i])
    allowed = tolerance(len(values))
    passed = drops <= allowed and (worst is None or worst[0] <= MAX_DROP_PCT)
    detail = f"{len(values)} anos; {plural(drops, 'queda', 'quedas')} (tolera {allowed}, de até {fmt_pct(MAX_DROP_PCT)})"
    if worst is not None:
        size = "piora de prejuízo" if math.isinf(worst[0]) else fmt_pct(worst[0])
        detail += f"; maior queda {size} em {worst[1]}"
    return passed, detail, passed and drops > 0


def cagr(years_desc: list[str], values_desc: list[float]) -> Optional[float]:
    if len(values_desc) < 2 or values_desc[-1] <= 0 or values_desc[0] <= 0:
        return None
    span = int(years_desc[0]) - int(years_desc[-1])
    return (values_desc[0] / values_desc[-1]) ** (1 / span) - 1 if span > 0 else None


def real_cagr(years_desc: list[str], nominal: Optional[float], ipca: dict[str, float]) -> Optional[float]:
    """Crescimento anual descontado o IPCA dos anos entre o primeiro e o último."""
    if nominal is None or len(years_desc) < 2:
        return None
    first, last = int(years_desc[-1]), int(years_desc[0])
    rates = [ipca.get(str(y)) for y in range(first + 1, last + 1)]
    if any(r is None for r in rates):
        return None
    inflation = math.prod(1 + r for r in rates)  # type: ignore[operator]
    return (1 + nominal) / inflation ** (1 / (last - first)) - 1


def consecutive_years(years_desc: list[str], series: list[dict[str, Optional[float]]]) -> list[str]:
    """Anos consecutivos, a partir do mais recente completo, com todas as séries preenchidas."""
    window: list[str] = []
    for year in years_desc:
        complete = all(s.get(year) is not None for s in series)
        if complete and (not window or int(window[-1]) - int(year) == 1):
            window.append(year)
        elif window:
            break
    return window


@dataclass
class Criterion:
    key: str
    label: str
    short: str
    passed: Optional[bool]  # None = dados insuficientes
    detail: str
    tolerado: bool = False  # passou só por causa da tolerância


def history_criterion(
    key: str, label: str, short: str, window: list[str], series: dict[str, Optional[float]],
    evaluate: Callable[[list[str], list[float]], Evaluation],
) -> Criterion:
    if len(window) < MIN_HISTORY_YEARS:
        return Criterion(key, label, short, None, f"{plural(len(window), 'ano completo', 'anos completos')}; mínimo {MIN_HISTORY_YEARS}")
    passed, detail, tolerated = evaluate(window, [float(series[y]) for y in window])  # type: ignore[arg-type]
    return Criterion(key, label, short, passed, detail, tolerated)


def require_real_growth(c: Criterion, real: Optional[float]) -> Criterion:
    """Crescer também acima da inflação: além de não cair ano a ano (em
    valores nominais), o crescimento real no período precisa ser ≥ 0."""
    if c.passed is None or real is None:
        return c
    sign = "+" if real > 0 else ""
    c.detail += f"; crescimento real de {sign}{fmt_pct(real)} ao ano no período (precisa ser ≥ 0)"
    if real < 0 and c.passed:
        c.passed, c.tolerado = False, False
    return c


def limit_criterion(key: str, label: str, short: str, value: Optional[float], ok: Callable[[float], bool], shown: str) -> Criterion:
    if value is None:
        return Criterion(key, label, short, None, "dado indisponível")
    return Criterion(key, label, short, ok(value), shown)


# ------------------------------------------------------------
# Qualidade do lucro
# ------------------------------------------------------------

@dataclass
class QualitySignal:
    key: str
    label: str
    nivel: str  # alto | medio | info
    detalhe: str


AUDIT_RED_FLAGS = {"Com Ressalva": "com ressalva", "Adverso": "adverso", "Negativa de Opinião": "com negativa de opinião"}


def earnings_quality(
    data: CompanyData, annual: dict[str, Flow], ends: dict[str, str], window: list[str], financeira: bool,
) -> tuple[list[QualitySignal], Optional[float], Optional[float], Optional[str]]:
    """Sinais de que o lucro pode não refletir a operação.

    Devolve (sinais, conversão de caixa, alíquota efetiva de IR, parecer do
    auditor). Nada aqui prova manipulação: são pontos para olhar nas notas
    explicativas e no release. A CVM não marca itens não recorrentes, então os
    sinais usam o que dá para medir nas demonstrações.
    """
    signals: list[QualitySignal] = []
    years = window if len(window) >= 2 else sorted(annual, reverse=True)[:3]
    conversion = effective_tax = None

    if years:
        latest_year = years[0]
        last = annual[latest_year]

        # 1. Lucro que não vira caixa (soma do período, para diluir o ruído de
        # capital de giro de um ano só). Não vale para bancos: o caixa
        # operacional deles mistura captações e empréstimos.
        if not financeira:
            profits = [annual[y].lucro for y in years]
            cash = [annual[y].fco for y in years]
            if all(v is not None for v in profits + cash) and sum(profits) > 0:  # type: ignore[arg-type]
                conversion = sum(cash) / sum(profits)  # type: ignore[arg-type]
                if conversion < 0.7:
                    signals.append(QualitySignal(
                        "caixa", "Lucro que não vira caixa", "alto" if conversion < 0.4 else "medio",
                        f"Em {len(years)} anos ({years[-1]}–{latest_year}), o caixa operacional somou {fmt_bi(sum(cash))}, "  # type: ignore[arg-type]
                        f"{fmt_pct(conversion)} do lucro de {fmt_bi(sum(profits))}. Pode ser venda a prazo crescente, "  # type: ignore[arg-type]
                        "estoque acumulando ou ganho contábil sem entrada de dinheiro."))

        # 2. Imposto: alíquota efetiva muito baixa ou crédito tributário
        # sustentando o lucro. A nominal é 34%; JCP e incentivos reduzem.
        lair, ir, profit = last.lair, last.ir, last.lucro
        if lair is not None and lair > 0 and ir is not None:
            effective_tax = -ir / lair
        if lair is not None and ir is not None and profit and profit > 0:
            if lair <= 0:
                signals.append(QualitySignal(
                    "ir", "Lucro sustentado por imposto", "alto",
                    f"Em {latest_year} o resultado antes dos tributos foi {fmt_bi(lair)}; o lucro de {fmt_bi(profit)} "
                    f"veio de um crédito de IR de {fmt_bi(ir)}."))
            elif ir > 0.2 * profit:
                signals.append(QualitySignal(
                    "ir", "Lucro sustentado por imposto", "alto",
                    f"Em {latest_year} o IR somou {fmt_bi(ir)} ao lucro em vez de descontar: {fmt_pct(ir / profit)} "
                    f"do lucro de {fmt_bi(profit)} veio de crédito tributário."))
            elif effective_tax is not None and effective_tax < 0.10:
                # Comum em quem paga muito JCP (bancos) ou vive de equivalência
                # (holdings): informativo, não conta como alerta.
                signals.append(QualitySignal(
                    "ir", "Alíquota efetiva de IR baixa", "info",
                    f"Em {latest_year} a alíquota efetiva foi {fmt_pct(effective_tax)} (nominal de 34%). JCP, equivalência "
                    "e incentivos costumam explicar; vale conferir se há crédito que não se repete."))
            elif last.ir_diferido and last.ir_diferido > 0.25 * profit:
                signals.append(QualitySignal(
                    "ir", "Crédito de IR diferido relevante", "medio",
                    f"Em {latest_year} o IR diferido somou {fmt_bi(last.ir_diferido)} ao lucro "
                    f"({fmt_pct(last.ir_diferido / profit)} do lucro): é contábil, não entra caixa."))

    if years and not financeira:
        # 3. Ganhos fora da operação: um aviso por tipo, com os anos em que apareceram.
        other_gains = [(y, annual[y].outras_operacionais / annual[y].ebit) for y in years  # type: ignore[operator]
                       if annual[y].outras_operacionais and (annual[y].ebit or 0) > 0
                       and annual[y].outras_operacionais > 0.25 * annual[y].ebit]  # type: ignore[operator]
        if other_gains:
            signals.append(QualitySignal(
                "nao_recorrente", "Outras receitas operacionais altas", "medio",
                "Outras receitas operacionais líquidas acima de 25% do EBIT em "
                + ", ".join(f"{y} ({fmt_pct(share)} do EBIT)" for y, share in sorted(other_gains))
                + ". Costumam ser venda de ativos, reversão de provisões ou créditos fiscais."))
        discontinued = [(y, annual[y].descontinuadas / annual[y].lucro) for y in years  # type: ignore[operator]
                        if annual[y].descontinuadas and (annual[y].lucro or 0) > 0
                        and annual[y].descontinuadas > 0.2 * annual[y].lucro]  # type: ignore[operator]
        if discontinued:
            signals.append(QualitySignal(
                "nao_recorrente", "Lucro de operações descontinuadas", "medio",
                "Parte relevante do lucro veio de operações descontinuadas (venda ou encerramento de negócios) em "
                + ", ".join(f"{y} ({fmt_pct(share)} do lucro)" for y, share in sorted(discontinued)) + "."))
        last = annual[years[0]]
        if last.equivalencia and last.lucro and last.lucro > 0 and last.equivalencia > 0.4 * last.lucro:
            signals.append(QualitySignal(
                "equivalencia", "Lucro vindo de participações", "info",
                f"Em {years[0]}, {fmt_pct(last.equivalencia / last.lucro)} do lucro veio de equivalência patrimonial "
                "(empresas em que tem participação). Normal em holdings; a qualidade depende das investidas."))

        # 4. Lucro crescendo bem mais que a operação.
        if len(years) >= 3:
            ebits = [annual[y].ebit for y in years]
            profits_ctrl = [annual[y].lucro_ctrl for y in years]
            if all(v is not None for v in ebits + profits_ctrl):
                g_ebit, g_profit = cagr(years, ebits), cagr(years, profits_ctrl)  # type: ignore[arg-type]
                if g_ebit is not None and g_profit is not None and g_profit - g_ebit > 0.10:
                    signals.append(QualitySignal(
                        "descolado", "Lucro crescendo mais que a operação", "medio",
                        f"De {years[-1]} a {years[0]} o lucro cresceu {fmt_pct(g_profit)} ao ano e o EBIT, "
                        f"{fmt_pct(g_ebit)}. A diferença veio de resultado financeiro, impostos ou itens fora da operação."))

        # 5. Recebíveis e estoques crescendo muito mais que a receita.
        first, latest = years[-1], years[0]
        b_first, b_last = data.balances.get(ends.get(first, "")), data.balances.get(ends.get(latest, ""))
        rev_first, rev_last = annual[first].receita, annual[latest].receita
        if b_first and b_last and rev_first and rev_last and rev_first > 0 and rev_last > 0:
            for attr, name in (("recebiveis", "Contas a receber"), ("estoques", "Estoques")):
                v_first, v_last = getattr(b_first, attr), getattr(b_last, attr)
                if v_first and v_last and v_first > 0 and v_last > 0.05 * rev_last:
                    ratio = (v_last / v_first) / (rev_last / rev_first)
                    if ratio > 1.5:
                        signals.append(QualitySignal(
                            attr, f"{name} crescendo mais que a receita", "medio",
                            f"De {first} a {latest}, {name.lower()} foram multiplicados por {fmt_num(v_last / v_first, 1)} "
                            f"e a receita por {fmt_num(rev_last / rev_first, 1)}. "
                            + ("Pode ser venda a prazo mais longa ou receita reconhecida antes de receber."
                               if attr == "recebiveis" else "Pode ser produto encalhado ou custo sendo segurado no estoque.")))

    # 6. Demonstrações reapresentadas (comum por motivos menores; vale conferir o motivo).
    redone = sorted(y for y in data.reapresentadas if y in years)
    if redone:
        signals.append(QualitySignal(
            "reapresentacao", "Demonstração reapresentada", "info",
            "DFP reapresentada à CVM: " + ", ".join(f"{y} (versão {data.reapresentadas[y]})" for y in redone)
            + ". Muitas vezes é ajuste menor; o motivo fica no documento."))

    # 7. Parecer do auditor.
    opinion = None
    if data.parecer:
        year, kind_of_report, going_concern = data.parecer
        opinion = kind_of_report + (" · incerteza sobre continuidade" if going_concern else "")
        if kind_of_report in AUDIT_RED_FLAGS:
            signals.append(QualitySignal(
                "auditor", "Parecer do auditor com problema", "alto",
                f"O relatório do auditor sobre a DFP de {year} foi {AUDIT_RED_FLAGS[kind_of_report]}."))
        if going_concern:
            signals.append(QualitySignal(
                "continuidade", "Dúvida sobre continuidade", "alto",
                f"O auditor apontou incerteza relevante sobre a continuidade operacional na DFP de {year}."))

    return signals, conversion, effective_tax, opinion


# ------------------------------------------------------------
# Análise de uma empresa
# ------------------------------------------------------------

@dataclass
class ScreenResult:
    ticker: str
    nome: str
    cnpj: str
    status: str = "erro"  # aprovada | margem | quase | reprovada | insuficiente | erro
    perfil: str = NAO_FINANCEIRA
    setor: Optional[str] = None
    outras_classes: list[str] = field(default_factory=list)
    fonte: Optional[str] = None  # documento mais recente na CVM
    site_ri: Optional[str] = None
    base: str = "consolidado"
    data_balanco: Optional[str] = None
    data_cotacao: Optional[str] = None
    preco: Optional[float] = None
    volume_medio: Optional[float] = None
    acoes: Optional[float] = None
    valor_mercado: Optional[float] = None
    base_valor_mercado: Optional[str] = None
    valuation_confiavel: bool = True
    enterprise_value: Optional[float] = None
    receita_12m: Optional[float] = None
    lucro_12m: Optional[float] = None
    ebitda_12m: Optional[float] = None
    divida_liquida: Optional[float] = None
    patrimonio_liquido: Optional[float] = None
    ativo_total: Optional[float] = None
    roe_12m: Optional[float] = None
    margem_12m: Optional[float] = None
    roa_12m: Optional[float] = None
    liquidez_corrente: Optional[float] = None
    divida_ebitda: Optional[float] = None
    divida_pl: Optional[float] = None
    capitalizacao: Optional[float] = None
    pl: Optional[float] = None
    pvp: Optional[float] = None
    ev_ebitda: Optional[float] = None
    earnings_yield: Optional[float] = None
    cagr_receita: Optional[float] = None
    cagr_lucro: Optional[float] = None
    cagr_receita_real: Optional[float] = None
    cagr_lucro_real: Optional[float] = None
    receita_rotulo: str = "Receita"  # bancos: "Intermediação"
    basileia: Optional[float] = None
    basileia_data: Optional[str] = None  # AAAAMM
    historico: dict[str, list] = field(default_factory=dict)
    anos_usados: list[str] = field(default_factory=list)
    criterios: list[Criterion] = field(default_factory=list)
    avisos: list[str] = field(default_factory=list)
    qualidade: list[QualitySignal] = field(default_factory=list)
    conversao_caixa: Optional[float] = None
    aliquota_efetiva: Optional[float] = None
    parecer_auditor: Optional[str] = None
    erro: Optional[str] = None


def class_price(quotes: list[Quote], classe: str) -> Optional[float]:
    same = [q for q in quotes if q.classe == classe]
    return max(same, key=lambda q: q.volume_medio).preco if same else None


def share_prices(quotes: list[Quote], unit_sizes: dict[str, int]) -> tuple[Optional[float], Optional[float], Optional[str]]:
    """(preço da ON, preço da PN, como foi obtido).

    Quando a unit é o papel mais líquido, as classes avulsas costumam ter
    poucos negócios e preços defasados (BTG: ON a R$ 22,19 e PN a R$ 17,61,
    mas a unit de 3 ações a R$ 51,52). Nesse caso cada ação vale unit ÷ ações
    por unit; a composição vem do cadastro ou é deduzida dos preços.
    """
    main = max(quotes, key=lambda q: q.volume_medio)
    on, pn = class_price(quotes, "ON"), class_price(quotes, "PN")
    if main.classe == "UNT":
        size = unit_sizes.get(main.ticker)
        others = [p for p in (on, pn) if p]
        if size is None and others:
            size = round(main.preco / (sum(others) / len(others))) or None
        if size:
            per_share = main.preco / size
            return per_share, per_share, f"{main.ticker} ÷ {size} ações"
    on, pn = on or pn, pn or on
    return on, pn, None


def analyze(
    company: Company, quotes: list[Quote], data: Optional[CompanyData], unit_sizes: dict[str, int], ipca: dict[str, float],
    basel: dict[str, float], basel_date: Optional[str],
) -> ScreenResult:
    main = max(quotes, key=lambda q: q.volume_medio)
    row = ScreenResult(
        ticker=main.ticker,
        nome=company.nome,
        cnpj=company.cnpj,
        setor=company.setor,
        site_ri=company.site_ri,
        outras_classes=sorted(q.ticker for q in quotes if q is not main),
        data_cotacao=main.data,
        preco=main.preco,
        volume_medio=main.volume_medio,
    )
    if data is None or not data.flows:
        row.erro = "Sem demonstrações financeiras na CVM para este CNPJ nos últimos anos."
        return row
    row.base = "consolidado" if data.consolidado else "individual"
    if data.ultimo_doc:
        row.fonte = data.ultimo_doc[1] or None
    if not data.consolidado:
        row.avisos.append("A empresa não publica demonstração consolidada; usada a individual.")
    elif data.periodos_individuais:
        row.avisos.append("Em alguns períodos o consolidado veio vazio na CVM; esses períodos usam a demonstração individual.")

    # Balanço mais recente e resultado dos últimos 12 meses.
    latest_date = max(data.balances) if data.balances else None
    current = data.balances[latest_date] if latest_date else Balance()
    row.data_balanco = latest_date
    ttm, _, approximate = trailing_twelve_months(data)
    ttm = ttm or Flow()
    if approximate:
        row.avisos.append("Últimos 12 meses aproximados pelo último exercício (faltou o trimestre comparável).")

    row.perfil = financial_profile(company.setor, ttm.receita_desc)
    financeira = row.perfil != NAO_FINANCEIRA
    bank_like = row.perfil in (BANCO, FINANCEIRA)
    if bank_like:
        row.basileia = basel.get(cnpj_root(company.cnpj))
        row.basileia_data = basel_date
        row.receita_rotulo = "Intermediação"
    row.receita_12m, row.lucro_12m, row.ebitda_12m = ttm.receita, ttm.lucro_ctrl, ttm.ebitda
    row.divida_liquida = current.divida_liquida
    row.patrimonio_liquido = current.pl_ctrl
    row.ativo_total = current.ativo
    row.roe_12m = safe_div(ttm.lucro_ctrl, current.pl_ctrl) if (current.pl_ctrl or 0) > 0 else None
    row.margem_12m = safe_div(ttm.lucro, ttm.receita) if (ttm.receita or 0) > 0 else None
    row.roa_12m = safe_div(ttm.lucro, current.ativo)
    row.liquidez_corrente = safe_div(current.ativo_circ, current.passivo_circ)
    row.capitalizacao = safe_div(current.pl, current.ativo) if (current.ativo or 0) > 0 else None

    # Histórico anual, do mais recente para o mais antigo.
    annual = annual_flows(data)
    ends = annual_end_dates(data)
    years = sorted(annual, reverse=True)[:MAX_HISTORY_YEARS]
    # Para bancos, o equivalente da receita é o resultado bruto da intermediação:
    # a receita de juros bruta sobe e desce com a Selic mesmo sem o banco crescer.
    receita = {y: annual[y].intermediacao if bank_like else annual[y].receita for y in years}
    lucro = {y: annual[y].lucro_ctrl for y in years}
    lucro_total = {y: annual[y].lucro for y in years}
    equity = {y: data.balances[ends[y]].pl_ctrl if ends[y] in data.balances else None for y in years}
    assets = {y: data.balances[ends[y]].ativo if ends[y] in data.balances else None for y in years}
    prev_equity, prev_assets = {}, {}
    for y in years:
        prev_end = shift_year(ends[y], -1)
        prev = data.balances.get(prev_end)
        prev_equity[y] = prev.pl_ctrl if prev else None
        prev_assets[y] = prev.ativo if prev else None

    def average(a: Optional[float], b: Optional[float]) -> Optional[float]:
        return a if b is None else (b if a is None else (a + b) / 2)

    roe = {y: safe_div(lucro[y], average(equity[y], prev_equity[y])) if (equity[y] or 0) > 0 else None for y in years}
    negative_equity = [y for y in years if equity[y] is not None and equity[y] <= 0]
    margem = {y: safe_div(lucro_total[y], receita[y]) if (receita[y] or 0) > 0 and not financeira else None for y in years}
    roa = {y: safe_div(lucro_total[y], average(assets[y], prev_assets[y])) for y in years}

    # Os critérios olham exercícios completos; avisa quando o ano corrente destoa.
    if years and ttm is not None and not approximate:
        last = annual[years[0]]
        if (last.lucro_ctrl or 0) > 0 and ttm.lucro_ctrl is not None and ttm.lucro_ctrl < 0.7 * last.lucro_ctrl:
            row.avisos.append(f"Lucro dos últimos 12 meses ({fmt_bi(ttm.lucro_ctrl)}) bem abaixo do exercício "
                              f"de {years[0]} ({fmt_bi(last.lucro_ctrl)}): os critérios ainda não captam essa piora.")
        if not financeira and (last.receita or 0) > 0 and ttm.receita and not 0.5 <= ttm.receita / last.receita <= 2:
            row.avisos.append(f"Receita dos últimos 12 meses ({fmt_bi(ttm.receita)}) muito diferente da de {years[0]} "
                              f"({fmt_bi(last.receita)}): provável reorganização societária; o histórico pode não ser comparável.")

    required = [lucro, equity] if financeira else [receita, lucro, equity, margem]
    window = consecutive_years(years, required)
    row.anos_usados = window
    chronological = years[::-1]
    row.historico = {
        "anos": chronological,
        "receita": [receita[y] for y in chronological],
        "lucro": [lucro[y] for y in chronological],
        "roe": [roe[y] for y in chronological],
        "margem": [margem[y] for y in chronological],
        "roa": [roa[y] for y in chronological],
    }
    if len(window) >= 2:
        row.cagr_lucro = cagr(window, [lucro[y] for y in window])  # type: ignore[misc]
        row.cagr_lucro_real = real_cagr(window, row.cagr_lucro, ipca)
    # Bancos podem ter a intermediação em menos anos que o lucro: janela própria.
    revenue_window = consecutive_years(years, [receita]) if bank_like else window
    if len(revenue_window) >= 2 and row.perfil not in (SEGURADORA, HOLDING):
        row.cagr_receita = cagr(revenue_window, [receita[y] for y in revenue_window])  # type: ignore[misc]
        row.cagr_receita_real = real_cagr(revenue_window, row.cagr_receita, ipca)

    bad_equity = [y for y in window if y in negative_equity]
    if bad_equity:
        roe_criterion = Criterion("roe", "ROE > 15%", "ROE", False,
                                  f"patrimônio líquido negativo em {', '.join(sorted(bad_equity))}: ROE sem sentido")
    else:
        roe_criterion = history_criterion("roe", "ROE > 15%", "ROE", window, roe,
                                          lambda y, v: evaluate_threshold(y, v, ROE_MIN, ROE_TOLERATED))
    criteria = [
        roe_criterion,
        require_real_growth(history_criterion("lucro", "Lucro crescente, acima da inflação", "Lucro",
                                              window, lucro, evaluate_growth), row.cagr_lucro_real),
    ]

    if not financeira:
        criteria += [
            require_real_growth(history_criterion("receita", "Receita crescente, acima da inflação", "Receita",
                                                  window, receita, evaluate_growth), row.cagr_receita_real),
            history_criterion("margem", "Margem líquida > 15%", "Margem", window, margem,
                              lambda y, v: evaluate_threshold(y, v, MARGIN_MIN, MARGIN_TOLERATED)),
        ]
        dl, ebitda, pl_total = current.divida_liquida, ttm.ebitda, current.pl
        row.divida_ebitda = safe_div(dl, ebitda) if (ebitda or 0) > 0 else None
        # Dívida/patrimônio fica só como informação: não faz parte do método.
        row.divida_pl = safe_div(dl, pl_total) if (pl_total or 0) > 0 else None
        if dl is None or ebitda is None:
            criteria.append(Criterion("div_ebitda", "Dívida líq./EBITDA < 3x", "Dív/EBITDA", None, "dado indisponível"))
        elif ebitda <= 0:
            criteria.append(Criterion("div_ebitda", "Dívida líq./EBITDA < 3x", "Dív/EBITDA", False, "EBITDA dos últimos 12 meses não positivo"))
        elif dl <= 0:
            criteria.append(Criterion("div_ebitda", "Dívida líq./EBITDA < 3x", "Dív/EBITDA", True, "caixa líquido (dívida líquida negativa)"))
        else:
            criteria.append(limit_criterion("div_ebitda", "Dívida líq./EBITDA < 3x", "Dív/EBITDA", row.divida_ebitda,
                                            lambda v: v < MAX_NET_DEBT_EBITDA, fmt_mult(row.divida_ebitda)))
    elif bank_like:
        # Mesmas ideias do método, com a métrica que funciona para banco:
        # vendas -> intermediação, margem -> ROA, dívida -> índice de Basileia.
        roa_window = consecutive_years(years, [roa])
        criteria += [
            require_real_growth(history_criterion("receita", "Resultado da intermediação crescente, acima da inflação",
                                                  "Intermediação", revenue_window, receita, evaluate_growth),
                                row.cagr_receita_real),
            history_criterion("roa", "ROA > 1%", "ROA", roa_window, roa,
                              lambda y, v: evaluate_threshold(y, v, ROA_MIN, ROA_TOLERATED)),
        ]
        when = f"{basel_date[4:]}/{basel_date[:4]}" if basel_date else ""
        if row.basileia is None:
            criteria.append(Criterion("basileia", f"Índice de Basileia ≥ {fmt_pct(BASEL_MIN)}", "Basileia", None,
                                      "não encontrado no IF.data do Banco Central para este CNPJ"))
        else:
            criteria.append(limit_criterion("basileia", f"Índice de Basileia ≥ {fmt_pct(BASEL_MIN)}", "Basileia", row.basileia,
                                            lambda v: v >= BASEL_MIN, f"{fmt_pct(row.basileia)} em {when} (Banco Central)"))
    else:
        # Seguradoras e holdings vivem do lucro de participações: sem receita,
        # margem ou dívida comparáveis nos dados da CVM. Ficam ROE e lucro.
        row.avisos.append("Critérios reduzidos: para seguradoras e holdings só ROE e lucro são comparáveis com o método.")
    row.criterios = criteria
    row.qualidade, row.conversao_caixa, row.aliquota_efetiva, row.parecer_auditor = earnings_quality(
        data, annual, ends, window, financeira)

    # Valuation: ações em circulação de cada classe × preço da classe.
    price_on, price_pn, via_unit = share_prices(quotes, unit_sizes)
    reference_price = price_on or price_pn
    on, pn, shares_warning = shares_outstanding(data, reference_price, current.pl_ctrl)
    if on is not None and pn is not None and price_on is not None and price_pn is not None:
        row.acoes = on + pn
        row.valor_mercado = on * price_on + pn * price_pn
        row.base_valor_mercado = f"preço por ação = {via_unit}" if via_unit else "preço de cada classe"
        if shares_warning:
            row.valuation_confiavel = False
            row.avisos.append(shares_warning)
        if not via_unit and ((on and not class_price(quotes, "ON")) or (pn and not class_price(quotes, "PN"))):
            row.avisos.append("Uma das classes não negocia no lote padrão; o valor de mercado usa o preço da outra classe para ela.")
    else:
        row.avisos.append("Sem composição do capital na CVM: valor de mercado e múltiplos indisponíveis.")
    vm = row.valor_mercado
    if vm:
        row.pl = safe_div(vm, ttm.lucro_ctrl)
        row.earnings_yield = safe_div(ttm.lucro_ctrl, vm)
        row.pvp = safe_div(vm, current.pl_ctrl) if (current.pl_ctrl or 0) > 0 else None
        if row.pvp is not None and not 0.05 <= row.pvp <= 20 and row.valuation_confiavel:
            row.valuation_confiavel = False
            row.avisos.append(f"P/VP atípico ({fmt_mult(row.pvp)}): o número de ações na CVM pode estar desatualizado "
                              "(grupamento, desdobramento ou aumento de capital recente). Confira o valuation.")
        if not financeira and current.divida_liquida is not None:
            row.enterprise_value = vm + current.divida_liquida + (current.pl_minor or 0.0)
            if (ttm.ebitda or 0) > 0:
                row.ev_ebitda = row.enterprise_value / ttm.ebitda  # type: ignore[operator]

    failed = sum(1 for c in criteria if c.passed is False)
    unknown = sum(1 for c in criteria if c.passed is None)
    if failed == 0 and unknown == 0:
        row.status = "margem" if any(c.tolerado for c in criteria) else "aprovada"
    elif failed == 1 and unknown == 0:
        row.status = "quase"
    elif failed:
        row.status = "reprovada"
    else:
        row.status = "insuficiente"
    return row


# ------------------------------------------------------------
# HTML
# ------------------------------------------------------------

def json_for_script(data: object) -> str:
    """JSON seguro dentro de <script>: sem NaN/Infinity e sem '</script>'."""
    def clean(value: object) -> object:
        if isinstance(value, float) and not math.isfinite(value):
            return None
        if isinstance(value, dict):
            return {k: clean(v) for k, v in value.items()}
        if isinstance(value, list):
            return [clean(v) for v in value]
        return value

    return (
        json.dumps(clean(data), ensure_ascii=False, allow_nan=False)
        .replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("&", "\\u0026")
        .replace(" ", "\\u2028")
        .replace(" ", "\\u2029")
    )


def write_html(results: list[ScreenResult], meta: dict, output_path: Path) -> None:
    payload = {"meta": meta, "results": [asdict(r) for r in results]}
    output_path.write_text(HTML_TEMPLATE.replace("__DATA_JSON__", json_for_script(payload)), encoding="utf-8")


HTML_TEMPLATE = r"""<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Screener B3</title>
<style>
  :root {
    color-scheme: light;
    --bg: #f6f7f9;
    --surface: #ffffff;
    --surface-2: #f1f3f6;
    --border: #e3e6eb;
    --text: #15181d;
    --muted: #5d6573;
    --faint: #8c94a2;
    --accent: #1f5fd1;
    --accent-soft: #eaf1fd;
    --ok: #157a3c;   --ok-soft: #e4f4ea;
    --mid: #0b7285;  --mid-soft: #e2f3f6;
    --warn: #a35a00; --warn-soft: #fdf2e1;
    --bad: #b42318;  --bad-soft: #fcebe9;
    --na: #8c94a2;   --na-soft: #eef0f3;
    --radius: 12px;
  }
  @media (prefers-color-scheme: dark) {
    :root:not([data-theme="light"]) {
      color-scheme: dark;
      --bg: #0f1115; --surface: #171a21; --surface-2: #1e222b; --border: #2a2f3a;
      --text: #e9ebef; --muted: #a3aab7; --faint: #6f7786;
      --accent: #74a6ff; --accent-soft: rgba(116, 166, 255, .14);
      --ok: #62d48e; --ok-soft: rgba(98, 212, 142, .14);
      --mid: #5ccad9; --mid-soft: rgba(92, 202, 217, .14);
      --warn: #f3b553; --warn-soft: rgba(243, 181, 83, .14);
      --bad: #ff8b80; --bad-soft: rgba(255, 139, 128, .14);
      --na: #7d8594; --na-soft: rgba(125, 133, 148, .16);
    }
  }
  :root[data-theme="dark"] {
    color-scheme: dark;
    --bg: #0f1115; --surface: #171a21; --surface-2: #1e222b; --border: #2a2f3a;
    --text: #e9ebef; --muted: #a3aab7; --faint: #6f7786;
    --accent: #74a6ff; --accent-soft: rgba(116, 166, 255, .14);
    --ok: #62d48e; --ok-soft: rgba(98, 212, 142, .14);
    --mid: #5ccad9; --mid-soft: rgba(92, 202, 217, .14);
    --warn: #f3b553; --warn-soft: rgba(243, 181, 83, .14);
    --bad: #ff8b80; --bad-soft: rgba(255, 139, 128, .14);
    --na: #7d8594; --na-soft: rgba(125, 133, 148, .16);
  }

  * { box-sizing: border-box; }
  [hidden] { display: none !important; }
  html { -webkit-text-size-adjust: 100%; }
  body {
    margin: 0; background: var(--bg); color: var(--text);
    font: 14px/1.5 system-ui, -apple-system, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
  }
  .container { max-width: 1200px; margin: 0 auto; padding: 32px 24px 56px; }
  .num { font-variant-numeric: tabular-nums; }
  .muted { color: var(--muted); }
  .sr-only { position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap; }
  a { color: var(--accent); text-decoration: none; }
  a:hover { text-decoration: underline; }
  button, input, select { font: inherit; color: inherit; }
  :focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; border-radius: 6px; }

  /* Cabeçalho */
  .top { display: flex; justify-content: space-between; align-items: flex-start; gap: 16px; }
  .eyebrow { margin: 0 0 6px; font-size: 13px; font-weight: 600; color: var(--muted); letter-spacing: .02em; }
  .lead { margin: 0; font-size: 24px; line-height: 1.3; font-weight: 600; letter-spacing: -.01em; max-width: 760px; }
  .lead strong { color: var(--ok); }
  .meta { margin: 8px 0 0; font-size: 13px; color: var(--muted); }
  .icon-btn {
    flex: none; width: 36px; height: 36px; display: inline-flex; align-items: center; justify-content: center;
    border: 1px solid var(--border); border-radius: 10px; background: var(--surface); cursor: pointer;
  }
  .icon-btn:hover { background: var(--surface-2); }
  .icon-btn svg { width: 18px; height: 18px; }

  .notice { margin-top: 16px; border: 1px solid var(--border); border-radius: 10px; background: var(--surface); font-size: 13px; }
  .notice summary { padding: 10px 14px; cursor: pointer; color: var(--warn); font-weight: 600; }
  .notice ul { margin: 0; padding: 0 14px 12px 32px; color: var(--muted); }

  /* Abas, busca e legenda */
  .controls { display: flex; flex-wrap: wrap; gap: 12px 16px; align-items: center; margin: 28px 0 12px; }
  .tabs { display: inline-flex; padding: 3px; gap: 2px; background: var(--surface-2); border-radius: 10px; }
  .tab {
    border: 0; background: transparent; padding: 7px 14px; border-radius: 8px; cursor: pointer;
    font-weight: 600; color: var(--muted); white-space: nowrap;
  }
  .tab:hover { color: var(--text); }
  .tab[aria-selected="true"] { background: var(--surface); color: var(--text); box-shadow: 0 1px 2px rgba(16, 24, 40, .08); }
  .tab .count { margin-left: 6px; font-weight: 500; color: var(--faint); }
  .search { position: relative; flex: 1 1 220px; max-width: 360px; }
  .search svg { position: absolute; left: 11px; top: 50%; transform: translateY(-50%); width: 16px; height: 16px; color: var(--faint); pointer-events: none; }
  .search input {
    width: 100%; height: 38px; padding: 0 12px 0 34px; border: 1px solid var(--border); border-radius: 10px; background: var(--surface);
  }
  .search input::placeholder { color: var(--faint); }
  .check { display: inline-flex; align-items: center; gap: 8px; color: var(--muted); cursor: pointer; user-select: none; }
  .check input { width: 16px; height: 16px; accent-color: var(--accent); }
  .spacer { flex: 1; }
  .link-btn { border: 0; background: none; color: var(--accent); cursor: pointer; padding: 6px 2px; font-weight: 500; }
  .link-btn:hover { text-decoration: underline; }
  .legend { display: flex; flex-wrap: wrap; gap: 6px 18px; margin: 0 0 12px; font-size: 12px; color: var(--muted); }
  .legend span { display: inline-flex; align-items: center; gap: 6px; }

  /* Marcas de critério */
  .mark {
    flex: none; display: inline-flex; align-items: center; justify-content: center; width: 18px; height: 18px;
    border-radius: 50%; font-size: 11px; font-weight: 700; line-height: 1;
  }
  .mark.ok { background: var(--ok-soft); color: var(--ok); }
  .mark.mid { background: var(--mid-soft); color: var(--mid); }
  .mark.bad { background: var(--bad-soft); color: var(--bad); }
  .mark.warn { background: var(--warn-soft); color: var(--warn); }
  .mark.na { background: var(--na-soft); color: var(--muted); }

  /* Tabela */
  .table-wrap { background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius); overflow-x: auto; }
  table { width: 100%; border-collapse: collapse; }
  thead th {
    position: sticky; top: 0; z-index: 1; background: var(--surface); padding: 0;
    border-bottom: 1px solid var(--border); text-align: left; font-size: 12px; font-weight: 600; color: var(--muted); white-space: nowrap;
  }
  th.num, td.num { text-align: right; }
  .sort-btn {
    display: inline-flex; flex-direction: column; align-items: inherit; gap: 1px; width: 100%; padding: 10px;
    border: 0; background: none; cursor: pointer; color: inherit; font-weight: 600; text-align: inherit;
  }
  th.num .sort-btn { align-items: flex-end; }
  .sort-btn:hover, th[aria-sort] .sort-btn { color: var(--text); }
  .sort-btn small { font-weight: 400; color: var(--faint); font-size: 11px; }
  .sort-arrow { margin-left: 4px; color: var(--accent); }
  tbody td { padding: 12px 10px; border-bottom: 1px solid var(--border); vertical-align: middle; white-space: nowrap; }
  tbody tr:last-child td { border-bottom: 0; }
  tbody td:first-child, thead th:first-child .sort-btn { padding-left: 14px; }
  tr.row { cursor: pointer; }
  tr.row:hover > td { background: var(--surface-2); }
  tr.row.open > td { background: var(--accent-soft); border-bottom-color: transparent; }

  .company { display: flex; align-items: center; gap: 10px; }
  .chevron { flex: none; width: 16px; height: 16px; color: var(--faint); transition: transform .15s; }
  tr.row.open .chevron { transform: rotate(90deg); color: var(--accent); }
  .ticker { font-weight: 700; }
  .name { display: block; max-width: 145px; overflow: hidden; text-overflow: ellipsis; font-size: 12px; color: var(--muted); }
  .tag { margin-left: 6px; padding: 1px 7px; border-radius: 999px; background: var(--na-soft); color: var(--muted); font-size: 11px; font-weight: 500; }
  .badge { display: inline-block; padding: 2px 9px; border-radius: 999px; font-size: 12px; font-weight: 600; }
  .badge.ok { background: var(--ok-soft); color: var(--ok); }
  .badge.mid { background: var(--mid-soft); color: var(--mid); }
  .badge.warn { background: var(--warn-soft); color: var(--warn); }
  .badge.bad { background: var(--bad-soft); color: var(--bad); }
  .badge.na { background: var(--na-soft); color: var(--muted); }
  .reason { display: block; margin-top: 3px; max-width: 165px; font-size: 12px; line-height: 1.35; color: var(--muted); white-space: normal; }
  .metric { display: inline-flex; align-items: center; gap: 7px; }
  .sub { display: block; font-size: 10.5px; color: var(--faint); }
  .dash { color: var(--faint); }
  .neg { color: var(--bad); }
  .doubt { color: var(--warn); cursor: help; }
  .alerts { display: inline-flex; gap: 6px; }
  .alert-dot { display: inline-flex; align-items: center; gap: 4px; padding: 2px 8px; border-radius: 999px; font-size: 12px; font-weight: 600; }
  .alert-dot.bad { background: var(--bad-soft); color: var(--bad); }
  .alert-dot.warn { background: var(--warn-soft); color: var(--warn); }

  /* Detalhes */
  tr.detail > td { padding: 0; background: var(--accent-soft); white-space: normal; }
  .detail-body {
    position: sticky; left: 0; width: var(--wrap-width, 100%);
    display: grid; grid-template-columns: minmax(0, 1.6fr) minmax(0, 1fr); gap: 14px; padding: 4px 14px 16px 40px;
  }
  .card { background: var(--surface); border: 1px solid var(--border); border-radius: 10px; padding: 16px 18px; min-width: 0; }
  .card + .card { margin-top: 14px; }
  .card h3 { margin: 0 0 12px; font-size: 13px; font-weight: 700; }
  .items { list-style: none; margin: 0; padding: 0; display: grid; gap: 12px; }
  .items li { display: grid; grid-template-columns: 18px 1fr; gap: 10px; }
  .item-title { font-weight: 600; }
  .item-text { display: block; margin-top: 1px; font-size: 12.5px; color: var(--muted); }
  .hist { width: 100%; border-collapse: collapse; font-size: 13px; }
  .hist-wrap { overflow-x: auto; }
  .hist th, .hist td { padding: 6px 7px; text-align: right; border-bottom: 1px solid var(--border); white-space: nowrap; }
  .hist th:first-child, .hist td:first-child { text-align: left; color: var(--muted); font-weight: 500; }
  .hist thead th { position: static; font-size: 12px; color: var(--muted); font-weight: 600; background: none; }
  .hist tr:last-child td { border-bottom: 0; }
  .hist .out { color: var(--faint); }
  .hist .spark { width: 84px; }
  .note { margin: 10px 0 0; font-size: 12px; color: var(--muted); }
  .kv { display: grid; grid-template-columns: auto 1fr; gap: 6px 16px; margin: 0; font-size: 13px; }
  .kv dt { color: var(--muted); white-space: nowrap; }
  .kv dd { margin: 0; text-align: right; font-variant-numeric: tabular-nums; }
  .kv .sep { grid-column: 1 / -1; height: 1px; background: var(--border); margin: 4px 0; }
  .links { margin: 14px 0 0; font-size: 13px; }
  .empty-state { padding: 48px 16px; text-align: center; color: var(--muted); }

  /* Como funciona */
  .method { margin-top: 20px; background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius); }
  .method summary { padding: 14px 18px; cursor: pointer; font-weight: 600; }
  .method-body { padding: 0 18px 18px; color: var(--muted); max-width: 860px; }
  .method-body h4 { margin: 16px 0 4px; color: var(--text); font-size: 13px; }
  .method-body ul { margin: 0; padding-left: 18px; }

  @media (max-width: 900px) {
    .detail-body { grid-template-columns: 1fr; padding-left: 14px; }
  }
  @media (max-width: 720px) {
    .container { padding: 20px 16px 40px; }
    .lead { font-size: 20px; }
    .tabs { width: 100%; }
    .tab { flex: 1; padding: 7px 8px; }
    .search { max-width: none; flex-basis: 100%; }
    .table-wrap { background: none; border: 0; overflow: visible; }
    table, tbody { display: block; }
    thead { display: none; }
    tr.row {
      display: grid; grid-template-columns: 1fr 1fr; gap: 8px 14px; margin-top: 10px; padding: 14px;
      background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius);
    }
    tr.row.open { border-radius: var(--radius) var(--radius) 0 0; }
    tr.row > td { display: flex; justify-content: space-between; align-items: center; gap: 8px; padding: 0; border: 0; background: none !important; }
    tr.row > td::before { content: attr(data-label); font-size: 12px; color: var(--muted); }
    tr.row > td.wide { grid-column: 1 / -1; display: block; }
    tr.row > td.wide::before { content: none; }
    .name, .reason { max-width: none; white-space: normal; }
    tr.detail { display: block; }
    tr.detail > td { display: block; border: 1px solid var(--border); border-top: 0; border-radius: 0 0 var(--radius) var(--radius); }
    .detail-body { position: static; width: auto; padding: 10px; }
  }
  @media (prefers-reduced-motion: reduce) { * { transition: none !important; } }
</style>
</head>
<body>
<div class="container">
  <header class="top">
    <div>
      <p class="eyebrow">Screener de qualidade · B3</p>
      <h1 class="lead" id="lead"></h1>
      <p class="meta" id="meta"></p>
    </div>
    <button class="icon-btn" id="themeToggle" type="button" aria-label="Alternar tema claro ou escuro" title="Alternar tema">
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/></svg>
    </button>
  </header>

  <details class="notice" id="notice" hidden><summary></summary><ul></ul></details>

  <div class="controls">
    <div class="tabs" role="tablist" aria-label="Resultado" id="tabs"></div>
    <label class="search">
      <span class="sr-only">Buscar</span>
      <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><circle cx="11" cy="11" r="7"/><path d="m20 20-3.5-3.5"/></svg>
      <input id="search" type="search" placeholder="Buscar empresa ou setor" autocomplete="off">
    </label>
    <label class="check"><input type="checkbox" id="hideRisk"> Esconder alertas altos</label>
    <span class="spacer"></span>
    <button class="link-btn" id="exportCsv" type="button">Baixar CSV</button>
  </div>
  <p class="legend" aria-hidden="true">
    <span><span class="mark ok">✓</span> cumpre</span>
    <span><span class="mark mid">≈</span> cumpre com tolerância</span>
    <span><span class="mark bad">✕</span> não cumpre</span>
    <span>Clique numa empresa para ver o porquê</span>
  </p>

  <div class="table-wrap">
    <table>
      <thead><tr id="head"></tr></thead>
      <tbody id="body"></tbody>
    </table>
    <div class="empty-state" id="empty" hidden></div>
  </div>

  <details class="method">
    <summary>Como funciona</summary>
    <div class="method-body" id="methodBody"></div>
  </details>
</div>

<script type="application/json" id="screener-data">__DATA_JSON__</script>
<script>
(() => {
  'use strict';
  const DATA = JSON.parse(document.getElementById('screener-data').textContent);
  const META = DATA.meta;
  const ROWS = DATA.results;

  // ---------- Formatação ----------
  const nf = (o) => new Intl.NumberFormat('pt-BR', o);
  const NF = {
    pct: nf({ style: 'percent', minimumFractionDigits: 1, maximumFractionDigits: 1 }),
    signed: nf({ style: 'percent', minimumFractionDigits: 1, maximumFractionDigits: 1, signDisplay: 'exceptZero' }),
    mult: nf({ minimumFractionDigits: 1, maximumFractionDigits: 1 }),
    compact: nf({ notation: 'compact', maximumFractionDigits: 1 }),
    price: nf({ style: 'currency', currency: 'BRL' }),
  };
  const isNum = (v) => typeof v === 'number' && Number.isFinite(v);
  const DASH = '<span class="dash">—</span>';
  const neg = (v, s) => (v < 0 ? `<span class="neg">${s}</span>` : s);
  const fmt = {
    pct: (v) => (isNum(v) ? neg(v, NF.pct.format(v)) : DASH),
    signed: (v) => (isNum(v) ? neg(v, NF.signed.format(v)) : DASH),
    mult: (v) => (isNum(v) ? neg(v, NF.mult.format(v) + 'x') : DASH),
    money: (v) => (isNum(v) ? neg(v, 'R$ ' + NF.compact.format(v)) : DASH),
    compact: (v) => (isNum(v) ? neg(v, NF.compact.format(v)) : DASH),
    price: (v) => (isNum(v) ? NF.price.format(v) : DASH),
  };
  const plain = (html) => html.replace(/<[^>]+>/g, '');
  const esc = (v) => String(v ?? '').replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
  const safeUrl = (v) => (/^https?:\/\//i.test(String(v || '')) ? esc(v) : '#');
  const fmtDate = (iso) => (iso ? new Date(`${iso}T12:00:00`).toLocaleDateString('pt-BR') : '—');

  // ---------- Modelo ----------
  const STATUS = {
    aprovada:     { label: 'Passa à risca',   tone: 'ok',   rank: 5 },
    margem:       { label: 'Passa na margem', tone: 'mid',  rank: 4 },
    quase:        { label: 'Falta 1',         tone: 'warn', rank: 3 },
    reprovada:    { label: 'Não passa',       tone: 'bad',  rank: 2 },
    insuficiente: { label: 'Histórico curto', tone: 'na',   rank: 1 },
    erro:         { label: 'Sem dados',       tone: 'na',   rank: 0 },
  };
  const TABS = [
    { key: 'passam', label: 'Passam', test: (r) => r.status === 'aprovada' || r.status === 'margem' },
    { key: 'quase', label: 'Falta 1 critério', test: (r) => r.status === 'quase' },
    { key: 'todas', label: 'Todas', test: () => true },
  ];
  const PROFILE = { banco: 'Banco', seguradora: 'Seguradora', financeira: 'Financeira', holding: 'Holding' };
  const isFin = (r) => r.perfil !== 'nao_financeira';
  // Bancos e financeiras têm métricas equivalentes; seguradoras e holdings, só ROE e lucro.
  const isBank = (r) => r.perfil === 'banco' || r.perfil === 'financeira';
  const isReduced = (r) => r.perfil === 'seguradora' || r.perfil === 'holding';
  const crit = (r, key) => r.criterios.find((c) => c.key === key);
  const alerts = (r) => ({
    alto: r.qualidade.filter((s) => s.nivel === 'alto').length,
    medio: r.qualidade.filter((s) => s.nivel === 'medio').length,
  });
  const names = (list) => list.map((c) => c.short).join(', ');

  function reason(r) {
    if (r.status === 'erro') return 'Sem demonstrações na CVM';
    if (r.status === 'aprovada') return isReduced(r) ? 'Só ROE e lucro se aplicam' : '';
    if (r.status === 'margem') return `Tolerância em ${names(r.criterios.filter((c) => c.tolerado))}`;
    const failed = r.criterios.filter((c) => c.passed === false);
    if (failed.length) return `Não cumpre: ${names(failed)}`;
    return 'Menos de 3 anos de histórico';
  }

  // Valor do pior ano dentro do período avaliado (é ele que decide o critério).
  function worstYear(r, series) {
    const used = new Set(r.anos_usados);
    const vals = r.historico.anos.map((y, i) => (used.has(y) ? r.historico[series][i] : null)).filter(isNum);
    return vals.length ? Math.min(...vals) : null;
  }

  function markFor(c) {
    if (!c) return '';
    const [cls, icon, word] = c.passed === true ? (c.tolerado ? ['mid', '≈', 'cumpre com tolerância'] : ['ok', '✓', 'cumpre'])
      : c.passed === false ? ['bad', '✕', 'não cumpre'] : ['na', '?', 'sem dados'];
    return `<span class="mark ${cls}" title="${esc(c.label)}: ${word}. ${esc(c.detail)}" role="img" aria-label="${word}">${icon}</span>`;
  }
  // Crescimento real (descontado o IPCA) em destaque, nominal embaixo.
  const realOr = (real, nominal) => (isNum(real) ? real : nominal);
  const growthCell = (real, nominal) => (isNum(real)
    ? `<span>${fmt.signed(real)}<span class="sub">nom. ${plain(fmt.signed(nominal))}</span></span>`
    : fmt.signed(nominal));
  const metric = (c, html) => `<span class="metric">${html}${markFor(c)}</span>`;
  const doubt = (r, html) => (r.valuation_confiavel || html === DASH ? html
    : `<span class="doubt" title="Número de ações incerto na CVM; veja os pontos de atenção">⚠ ${html}</span>`);
  const NA = '<span class="dash" title="Não se aplica a seguradoras e holdings: o lucro delas vem de participações">n/a</span>';
  // Para bancos, a coluna mostra a métrica equivalente, com o nome dela embaixo.
  const named = (html, name) => `<span>${html}<span class="sub">${name}</span></span>`;

  // ---------- Colunas ----------
  const COLUMNS = [
    { key: 'empresa', label: 'Empresa', cls: 'wide', dir: 'asc', value: (r) => r.ticker,
      render: (r) => `<div class="company">
        <svg class="chevron" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><path d="m6 3 5 5-5 5"/></svg>
        <div><span class="ticker">${esc(r.ticker)}</span>${PROFILE[r.perfil] ? `<span class="tag">${PROFILE[r.perfil]}</span>` : ''}
        <span class="name" title="${esc(r.nome)}">${esc(r.nome)}</span></div></div>` },
    { key: 'resultado', label: 'Resultado', cls: 'wide', dir: 'desc',
      value: (r) => STATUS[r.status].rank * 100 - alerts(r).alto * 10 - alerts(r).medio,
      render: (r) => `<span class="badge ${STATUS[r.status].tone}">${STATUS[r.status].label}</span>
        ${reason(r) ? `<span class="reason">${esc(reason(r))}</span>` : ''}` },
    { key: 'roe', label: 'ROE', hint: 'pior ano', num: true, dir: 'desc', value: (r) => worstYear(r, 'roe'),
      render: (r) => metric(crit(r, 'roe'), fmt.pct(worstYear(r, 'roe'))) },
    { key: 'margem', label: 'Margem líq.', hint: 'pior ano', num: true, dir: 'desc',
      value: (r) => (isFin(r) ? null : worstYear(r, 'margem')),
      render: (r) => (isReduced(r) ? NA : isBank(r) ? metric(crit(r, 'roa'), named(fmt.pct(worstYear(r, 'roa')), 'ROA'))
        : metric(crit(r, 'margem'), fmt.pct(worstYear(r, 'margem')))) },
    { key: 'receita', label: 'Receita', hint: 'cresc. real/ano', num: true, dir: 'desc',
      value: (r) => (isReduced(r) ? null : realOr(r.cagr_receita_real, r.cagr_receita)),
      render: (r) => (isReduced(r) ? NA : metric(crit(r, 'receita'), isBank(r)
        ? named(fmt.signed(realOr(r.cagr_receita_real, r.cagr_receita)), 'intermediação')
        : growthCell(r.cagr_receita_real, r.cagr_receita))) },
    { key: 'lucro', label: 'Lucro', hint: 'cresc. real/ano', num: true, dir: 'desc', value: (r) => realOr(r.cagr_lucro_real, r.cagr_lucro),
      render: (r) => metric(crit(r, 'lucro'), growthCell(r.cagr_lucro_real, r.cagr_lucro)) },
    { key: 'divida', label: 'Dív./EBITDA', hint: 'hoje', num: true, dir: 'asc',
      value: (r) => (isFin(r) ? null : (isNum(r.divida_liquida) && r.divida_liquida <= 0 && r.ebitda_12m > 0 ? -1 : r.divida_ebitda)),
      render: (r) => (isReduced(r) ? NA : isBank(r) ? metric(crit(r, 'basileia'), named(fmt.pct(r.basileia), 'Basileia'))
        : metric(crit(r, 'div_ebitda'),
          isNum(r.divida_liquida) && r.divida_liquida <= 0 && r.ebitda_12m > 0 ? '<span class="muted">caixa líq.</span>' : fmt.mult(r.divida_ebitda))) },
    { key: 'pl', label: 'P/L', hint: 'hoje', num: true, dir: 'asc', value: (r) => (isNum(r.pl) && r.pl > 0 ? r.pl : null),
      render: (r) => doubt(r, fmt.mult(r.pl)) },
    { key: 'alertas', label: 'Alertas', hint: 'do lucro', dir: 'asc', cls: 'alerts-cell',
      value: (r) => (r.status === 'erro' ? null : alerts(r).alto * 10 + alerts(r).medio),
      render: (r) => {
        const { alto, medio } = alerts(r);
        if (!alto && !medio) return DASH;
        const tip = r.qualidade.filter((s) => s.nivel !== 'info').map((s) => `${s.nivel === 'alto' ? 'Alto' : 'Médio'}: ${s.label}`).join(' · ');
        const total = alto + medio;
        return `<span class="alert-dot ${alto ? 'bad' : 'warn'}" title="${esc(tip)}">${total} ${total > 1 ? 'alertas' : 'alerta'}</span>`;
      } },
  ];

  // ---------- Estado ----------
  const state = { tab: 'passam', q: '', hideRisk: false, sortKey: 'resultado', sortDir: 'desc', open: new Set() };

  // ---------- Tema ----------
  const root = document.documentElement;
  try { const t = localStorage.getItem('b3-screener-theme'); if (t) root.dataset.theme = t; } catch (e) { /* sem storage */ }
  document.getElementById('themeToggle').addEventListener('click', () => {
    const current = root.dataset.theme || (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
    root.dataset.theme = current === 'dark' ? 'light' : 'dark';
    try { localStorage.setItem('b3-screener-theme', root.dataset.theme); } catch (e) { /* sem storage */ }
  });

  // ---------- Resumo ----------
  const count = (fn) => ROWS.filter(fn).length;
  const strict = count((r) => r.status === 'aprovada'), marginal = count((r) => r.status === 'margem');
  document.getElementById('lead').innerHTML =
    `<strong>${strict + marginal}</strong> das ${META.analisadas} empresas com liquidez passam no método`;
  document.getElementById('meta').textContent =
    `${strict} à risca e ${marginal} na margem · cotações até ${fmtDate(META.ultimo_pregao)} · ` +
    `gerado em ${new Date(META.gerado_em).toLocaleString('pt-BR', { dateStyle: 'short', timeStyle: 'short' })} · dados da CVM e da B3`;
  if (META.avisos.length) {
    const notice = document.getElementById('notice');
    notice.hidden = false;
    notice.querySelector('summary').textContent = `${META.avisos.length} aviso${META.avisos.length > 1 ? 's' : ''} sobre a coleta dos dados`;
    notice.querySelector('ul').innerHTML = META.avisos.map((a) => `<li>${esc(a)}</li>`).join('');
  }

  // ---------- Abas ----------
  function renderTabs() {
    document.getElementById('tabs').innerHTML = TABS.map((t) => `
      <button class="tab" role="tab" type="button" data-tab="${t.key}" aria-selected="${state.tab === t.key}">
        ${t.label}<span class="count num">${count(t.test)}</span></button>`).join('');
  }
  document.getElementById('tabs').addEventListener('click', (e) => {
    const b = e.target.closest('.tab');
    if (!b) return;
    state.tab = b.dataset.tab;
    renderTabs(); render();
  });

  // ---------- Cabeçalho da tabela ----------
  function renderHead() {
    document.getElementById('head').innerHTML = COLUMNS.map((c) => {
      const sorted = state.sortKey === c.key;
      const aria = sorted ? ` aria-sort="${state.sortDir === 'asc' ? 'ascending' : 'descending'}"` : '';
      return `<th scope="col" class="${c.num ? 'num' : ''}"${aria}><button class="sort-btn" type="button" data-key="${c.key}">
        <span>${c.label}${sorted ? `<span class="sort-arrow" aria-hidden="true">${state.sortDir === 'asc' ? '↑' : '↓'}</span>` : ''}</span>
        ${c.hint ? `<small>${c.hint}</small>` : ''}</button></th>`;
    }).join('');
  }
  document.getElementById('head').addEventListener('click', (e) => {
    const b = e.target.closest('.sort-btn');
    if (!b) return;
    const col = COLUMNS.find((c) => c.key === b.dataset.key);
    if (state.sortKey === col.key) state.sortDir = state.sortDir === 'asc' ? 'desc' : 'asc';
    else { state.sortKey = col.key; state.sortDir = col.dir; }
    render();
  });

  // ---------- Detalhes ----------
  function sparkline(values) {
    const pts = values.map((v, i) => [i, v]).filter(([, v]) => isNum(v));
    if (pts.length < 2) return '';
    const w = 72, h = 22, n = values.length - 1 || 1;
    const vs = pts.map(([, v]) => v), lo = Math.min(...vs), span = Math.max(...vs) - lo || 1;
    const xy = pts.map(([i, v]) => `${(i / n * w).toFixed(1)},${(h - 3 - (v - lo) / span * (h - 6)).toFixed(1)}`);
    const [lx, ly] = xy[xy.length - 1].split(',');
    return `<svg width="${w + 4}" height="${h}" viewBox="-2 0 ${w + 4} ${h}" aria-hidden="true">
      <polyline points="${xy.join(' ')}" fill="none" stroke="var(--accent)" stroke-width="1.5" stroke-linejoin="round" stroke-linecap="round"/>
      <circle cx="${lx}" cy="${ly}" r="2.2" fill="var(--accent)"/></svg>`;
  }

  // Avisos de dados e sinais de qualidade do lucro numa lista só, do mais grave ao informativo.
  function attention(r) {
    const level = { alto: 0, medio: 1, aviso: 2, info: 3 };
    const items = [
      ...r.qualidade.map((s) => ({ nivel: s.nivel, title: s.label, text: s.detalhe })),
      ...r.avisos.map((a) => ({ nivel: 'aviso', title: 'Sobre os dados', text: a })),
    ].sort((a, b) => level[a.nivel] - level[b.nivel]);
    if (!items.length) return '<p class="muted">Nada a destacar nas demonstrações.</p>';
    const look = { alto: ['bad', '!'], medio: ['warn', '!'], aviso: ['warn', 'i'], info: ['na', 'i'] };
    return `<ul class="items">${items.map((it) => {
      const [cls, icon] = look[it.nivel];
      return `<li><span class="mark ${cls}" aria-hidden="true">${icon}</span>
        <div><span class="item-title">${esc(it.title)}</span><span class="item-text">${esc(it.text)}</span></div></li>`;
    }).join('')}</ul>`;
  }

  function renderDetail(r) {
    const links = [
      r.fonte ? `<a href="${safeUrl(r.fonte)}" target="_blank" rel="noopener noreferrer">Demonstração na CVM ↗</a>` : '',
      r.site_ri ? `<a href="${safeUrl(r.site_ri)}" target="_blank" rel="noopener noreferrer">Site de RI ↗</a>` : '',
    ].filter(Boolean).join(' · ');
    if (r.status === 'erro') {
      return `<div class="detail-body"><div class="card">${esc(r.erro)}<p class="links">${links}</p></div></div>`;
    }

    const criteria = `<ul class="items">${r.criterios.map((c) => `<li>${markFor(c)}
      <div><span class="item-title">${esc(c.label)}</span><span class="item-text">${c.tolerado ? 'Passou pela tolerância. ' : ''}${esc(c.detail)}</span></div></li>`).join('')}</ul>`;

    const h = r.historico, used = new Set(r.anos_usados);
    const rows = [
      [`${r.receita_rotulo}, R$`, h.receita, fmt.compact, true],
      ['Lucro, R$', h.lucro, fmt.compact, true],
      ['ROE', h.roe, fmt.pct, false],
      isFin(r) ? ['ROA', h.roa, fmt.pct, false] : ['Margem líq.', h.margem, fmt.pct, false],
    ];
    const growth = isNum(r.cagr_lucro) ? `<p class="note">Crescimento ao ano no período, real (descontado o IPCA) e nominal:
      ${isNum(r.cagr_receita) ? `receita ${isNum(r.cagr_receita_real) ? plain(fmt.signed(r.cagr_receita_real)) : '—'} real, ${plain(fmt.signed(r.cagr_receita))} nominal; ` : ''}lucro ${isNum(r.cagr_lucro_real) ? plain(fmt.signed(r.cagr_lucro_real)) : '—'} real, ${plain(fmt.signed(r.cagr_lucro))} nominal.</p>` : '';
    const history = h.anos.length ? `<div class="hist-wrap"><table class="hist num">
        <thead><tr><th scope="col"></th>${h.anos.map((y) => `<th scope="col" class="${used.has(y) ? '' : 'out'}">${esc(y)}</th>`).join('')}<th></th></tr></thead>
        <tbody>${rows.map(([label, vals, f, spark]) => `<tr><td>${label}</td>${vals.map((v, i) =>
          `<td class="${used.has(h.anos[i]) ? '' : 'out'}">${f(v)}</td>`).join('')}<td class="spark">${spark ? sparkline(vals) : ''}</td></tr>`).join('')}</tbody>
      </table></div>${growth}` : '<p class="muted">Sem histórico anual.</p>';

    const kv = (pairs) => pairs.map((p) => (p === '-' ? '<div class="sep"></div>' : `<dt>${p[0]}</dt><dd>${p[1]}</dd>`)).join('');
    const numbers = `<dl class="kv">${kv([
      ['Preço', `${fmt.price(r.preco)} <span class="muted">${esc(r.ticker)}</span>`],
      ['Valor de mercado', doubt(r, fmt.money(r.valor_mercado))],
      ['P/L', doubt(r, fmt.mult(r.pl))], ['P/VP', doubt(r, fmt.mult(r.pvp))],
      ...(isFin(r) ? [] : [['EV/EBITDA', doubt(r, fmt.mult(r.ev_ebitda))]]),
      ['Earnings yield', doubt(r, fmt.pct(r.earnings_yield))],
      '-',
      ['Lucro (12 meses)', fmt.money(r.lucro_12m)],
      ...(isFin(r)
        ? [...(isBank(r) ? [['Índice de Basileia', isNum(r.basileia)
              ? `${plain(fmt.pct(r.basileia))} <span class="muted">${r.basileia_data ? `${r.basileia_data.slice(4)}/${r.basileia_data.slice(0, 4)}` : ''}</span>` : DASH]] : []),
           ['Patrimônio ÷ ativo', fmt.pct(r.capitalizacao)], ['ROA (12 meses)', fmt.pct(r.roa_12m)]]
        : [['Dívida líquida', fmt.money(r.divida_liquida)], ['Caixa operacional ÷ lucro', fmt.pct(r.conversao_caixa)]]),
      ['Alíquota efetiva de IR', fmt.pct(r.aliquota_efetiva)],
      ['Parecer do auditor', esc(r.parecer_auditor || '—')],
      '-',
      ['Setor', esc(r.setor || '—')],
      ['Volume médio', fmt.money(r.volume_medio)],
      ['Último balanço', `${fmtDate(r.data_balanco)}${r.base === 'individual' ? ' · individual' : ''}`],
      ...(r.outras_classes.length ? [['Outras classes', esc(r.outras_classes.join(', '))]] : []),
    ])}</dl><p class="links">${links}</p>`;

    return `<div class="detail-body">
      <div>
        <section class="card"><h3>Critérios do método</h3>${criteria}</section>
        <section class="card"><h3>Histórico</h3>${history}</section>
      </div>
      <div>
        <section class="card"><h3>Pontos de atenção</h3>${attention(r)}</section>
        <section class="card"><h3>Números</h3>${numbers}</section>
      </div></div>`;
  }

  // ---------- Lista ----------
  const missing = (v) => v === null || v === undefined || (typeof v === 'number' && !Number.isFinite(v));
  function visible() {
    const tab = TABS.find((t) => t.key === state.tab);
    const q = state.q.trim().toLocaleLowerCase('pt-BR');
    const col = COLUMNS.find((c) => c.key === state.sortKey);
    const dir = state.sortDir === 'asc' ? 1 : -1;
    return ROWS
      .filter(tab.test)
      .filter((r) => !state.hideRisk || alerts(r).alto === 0)
      .filter((r) => !q || [r.ticker, r.nome, r.setor, ...r.outras_classes].join(' ').toLocaleLowerCase('pt-BR').includes(q))
      .sort((a, b) => {
        const av = col.value(a), bv = col.value(b);
        if (missing(av) || missing(bv)) return missing(av) && missing(bv) ? a.ticker.localeCompare(b.ticker) : missing(av) ? 1 : -1;
        const cmp = typeof av === 'string' ? av.localeCompare(bv, 'pt-BR') : av - bv;
        return cmp ? cmp * dir : a.ticker.localeCompare(b.ticker);
      });
  }

  let current = [];
  function render() {
    current = visible();
    renderHead();
    document.getElementById('body').innerHTML = current.map((r) => {
      const open = state.open.has(r.ticker);
      const cells = COLUMNS.map((c) => `<td class="${c.num ? 'num' : ''} ${c.cls || ''}" data-label="${esc(c.label)}">${c.render(r)}</td>`).join('');
      return `<tr class="row${open ? ' open' : ''}" data-ticker="${esc(r.ticker)}" tabindex="0" aria-expanded="${open}">${cells}</tr>`
        + (open ? `<tr class="detail"><td colspan="${COLUMNS.length}">${renderDetail(r)}</td></tr>` : '');
    }).join('');
    const empty = document.getElementById('empty');
    empty.hidden = current.length > 0;
    if (!current.length) {
      empty.innerHTML = state.q || state.hideRisk
        ? 'Nenhuma empresa com esses filtros. <button class="link-btn" type="button" id="clear">Limpar filtros</button>'
        : 'Nenhuma empresa nesta aba.';
    }
  }

  function toggle(ticker) {
    if (state.open.has(ticker)) state.open.delete(ticker); else state.open.add(ticker);
    render();
    document.querySelector(`tr.row[data-ticker="${CSS.escape(ticker)}"]`)?.focus({ preventScroll: true });
  }
  const body = document.getElementById('body');
  body.addEventListener('click', (e) => {
    if (e.target.closest('a')) return;
    const tr = e.target.closest('tr.row');
    if (tr) toggle(tr.dataset.ticker);
  });
  body.addEventListener('keydown', (e) => {
    const tr = e.target.closest('tr.row');
    if (tr && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); toggle(tr.dataset.ticker); }
  });

  const search = document.getElementById('search');
  search.addEventListener('input', () => { state.q = search.value; render(); });
  document.getElementById('hideRisk').addEventListener('change', (e) => { state.hideRisk = e.target.checked; render(); });
  document.getElementById('empty').addEventListener('click', (e) => {
    if (e.target.id !== 'clear') return;
    state.q = ''; search.value = ''; state.hideRisk = false; document.getElementById('hideRisk').checked = false; render();
  });
  document.addEventListener('keydown', (e) => {
    if (e.key === '/' && !/^(INPUT|SELECT|TEXTAREA)$/.test(document.activeElement.tagName)) { e.preventDefault(); search.focus(); }
  });

  // ---------- CSV (Excel em português: ';' e vírgula decimal) ----------
  document.getElementById('exportCsv').addEventListener('click', () => {
    const num = (v, d = 4) => (isNum(v) ? v.toFixed(d).replace('.', ',') : '');
    const header = ['Ticker', 'Empresa', 'Setor', 'Resultado', 'Motivo', 'ROE pior ano', 'Margem pior ano',
      'Cresc. receita a.a.', 'Cresc. receita real a.a.', 'Cresc. lucro a.a.', 'Cresc. lucro real a.a.', 'Dív. líq./EBITDA',
      'P/L', 'P/VP', 'EV/EBITDA', 'Earnings yield', 'Valor de mercado', 'Valuation confiável', 'Alertas altos', 'Alertas médios',
      'Pontos de atenção', 'Caixa operacional ÷ lucro', 'Alíquota efetiva IR', 'Parecer do auditor', 'Volume médio', 'Demonstração na CVM'];
    const lines = current.map((r) => [
      r.ticker, r.nome, r.setor || '', STATUS[r.status].label, reason(r),
      num(worstYear(r, 'roe')), isFin(r) ? '' : num(worstYear(r, 'margem')),
      num(r.cagr_receita), num(r.cagr_receita_real), num(r.cagr_lucro), num(r.cagr_lucro_real), num(r.divida_ebitda, 2),
      num(r.pl, 2), num(r.pvp, 2), num(r.ev_ebitda, 2), num(r.earnings_yield), num(r.valor_mercado, 0),
      r.valuation_confiavel ? 'sim' : 'não', alerts(r).alto, alerts(r).medio,
      [...r.qualidade.map((s) => `[${s.nivel}] ${s.label}: ${s.detalhe}`), ...r.avisos].join(' | '),
      num(r.conversao_caixa), num(r.aliquota_efetiva), r.parecer_auditor || '', num(r.volume_medio, 0), r.fonte || '',
    ]);
    const csv = [header, ...lines].map((row) => row.map((v) => `"${String(v ?? '').replace(/"/g, '""')}"`).join(';')).join('\r\n');
    const url = URL.createObjectURL(new Blob(['﻿' + csv], { type: 'text/csv;charset=utf-8' }));
    const a = Object.assign(document.createElement('a'), { href: url, download: `screener-b3-${META.gerado_em.slice(0, 10)}.csv` });
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  });

  // ---------- Como funciona ----------
  const L = META.limites;
  const p = (v) => plain(fmt.pct(v)).replace(',0%', '%');
  document.getElementById('methodBody').innerHTML = `
    <h4>O método</h4>
    <ul><li>ROE acima de ${p(L.roe)} e margem líquida acima de ${p(L.margem)} em todos os anos.</li>
        <li>Receita e lucro crescentes: nenhuma queda de um ano para o outro e crescimento médio no período acima da inflação (crescimento real ≥ 0).</li>
        <li>Dívida líquida abaixo de ${L.divida_ebitda} vezes o EBITDA dos últimos 12 meses.</li>
        <li>Avalia os últimos ${META.anos_max} exercícios completos (mínimo de ${META.anos_min}).</li></ul>
    <h4>À risca, na margem e falta 1</h4>
    <ul><li><strong>À risca:</strong> cumpre tudo, sem exceção.</li>
        <li><strong>Na margem:</strong> cumpre usando a tolerância: ROE ou margem entre ${p(L.roe_tolerado)} e ${p(L.roe)}, ou quedas de até ${p(L.queda)} na receita ou no lucro, em 1 ano (com 3 ou 4 anos de histórico) ou 2 anos (com 5).</li>
        <li><strong>Falta 1:</strong> não cumpre exatamente um critério.</li></ul>
    <h4>Bancos</h4>
    <ul><li>As mesmas ideias, com a métrica que funciona para banco: ROE acima de ${p(L.roe)}; <strong>ROA</strong> acima de ${p(L.roa)} no lugar da margem (quanto do que o banco empresta vira lucro); <strong>índice de Basileia</strong> de pelo menos ${p(L.basileia)} no lugar da dívida (folga de capital sobre o mínimo regulatório de 10,5%, dado do Banco Central); <strong>resultado da intermediação</strong> crescente no lugar da receita (juros recebidos − custo de captação − provisões); lucro crescente.</li>
        <li>A receita de juros bruta não serve: sobe e desce com a Selic mesmo sem o banco crescer.</li></ul>
    <h4>Seguradoras e holdings</h4>
    <ul><li>BB Seguridade, Caixa Seguridade, Itaúsa e afins vivem do lucro de participações em outras empresas. Não têm receita, margem nem dívida comparáveis nos dados da CVM: valem só ROE e lucro crescente.</li></ul>
    <h4>Alertas de qualidade do lucro</h4>
    <ul><li>Não mudam o resultado: indicam onde ler as notas explicativas com cuidado.</li>
        <li><strong>Altos:</strong> caixa operacional abaixo de 40% do lucro; lucro sustentado por crédito de imposto; parecer do auditor com ressalva, adverso ou sem opinião; dúvida sobre a continuidade da empresa.</li>
        <li><strong>Médios:</strong> caixa entre 40% e 70% do lucro; imposto diferido acima de 25% do lucro; ganhos fora da operação relevantes; lucro crescendo muito mais que o EBIT; contas a receber ou estoques crescendo muito mais que a receita.</li></ul>
    <h4>Números</h4>
    <ul><li>Fontes: demonstrações consolidadas entregues à CVM, cotações da B3 e IPCA do Banco Central (${Object.entries(META.ipca).map(([y, v]) => `${y}: ${p(v)}`).join(', ')}).</li>
        <li>Entram empresas com volume médio de pelo menos ${plain(fmt.money(META.volume_minimo))} por pregão nos últimos ${META.pregoes} pregões.</li>
        <li>ROE e margem na tabela mostram o pior ano do período, que é o que decide o critério. O histórico completo está nos detalhes.</li>
        <li>Valor de mercado soma cada classe de ação pelo seu preço. ⚠ indica número de ações incerto na CVM.</li></ul>`;

  // O painel de detalhes acompanha a largura visível quando a tabela rola para o lado.
  const wrap = document.querySelector('.table-wrap');
  const syncWidth = () => wrap.style.setProperty('--wrap-width', `${wrap.clientWidth}px`);
  new ResizeObserver(syncWidth).observe(wrap);
  window.addEventListener('resize', syncWidth);
  syncWidth();

  renderTabs();
  render();
})();
</script>
</body>
</html>
"""


# ------------------------------------------------------------
# Execução
# ------------------------------------------------------------

def run(args: argparse.Namespace) -> list[ScreenResult]:
    start = time.time()
    today = date.today()
    dl = Downloader(args.cache_dir, args.cache_hours, args.refresh)
    warnings: list[str] = []

    print("Cotações da B3...", flush=True)
    quotes, last_session = load_quotes(dl, args.sessions, today)
    print("Cadastro da CVM...", flush=True)
    by_ticker, companies, unit_sizes = load_registry(dl, today.year)

    by_company: dict[str, list[Quote]] = {}
    unmapped: list[Quote] = []
    for quote in quotes.values():
        cnpj = resolve_cnpj(quote.ticker, by_ticker)
        if cnpj and cnpj in companies:
            by_company.setdefault(cnpj, []).append(quote)
        else:
            unmapped.append(quote)

    if args.tickers:
        wanted = {t.upper() for t in args.tickers}
        selected = {c: qs for c, qs in by_company.items() if wanted & {q.ticker for q in qs}}
        missing = wanted - {q.ticker for qs in selected.values() for q in qs}
        if missing:
            print(f"Aviso: sem cotação ou sem CNPJ na CVM, ignorados: {', '.join(sorted(missing))}", file=sys.stderr)
    else:
        selected = {c: qs for c, qs in by_company.items() if max(q.volume_medio for q in qs) >= args.min_volume}
        liquid_unmapped = sorted(q.ticker for q in unmapped if q.volume_medio >= args.min_volume)
        if liquid_unmapped:
            warnings.append("Tickers líquidos sem CNPJ no cadastro da CVM (fora da análise): " + ", ".join(liquid_unmapped) + ".")
    print(f"Empresas com volume médio ≥ R$ {fmt_num(args.min_volume, 0)}: {len(selected)} de {len(by_company)}", flush=True)

    print("Demonstrações financeiras da CVM...", flush=True)
    fundamentals = load_fundamentals(dl, set(selected), today)

    print("IPCA do Banco Central...", flush=True)
    try:
        ipca = load_ipca(dl, today)
    except (requests.RequestException, ValueError, KeyError) as exc:
        ipca = {}
        warnings.append(f"Não consegui baixar o IPCA ({type(exc).__name__}); crescimento real indisponível.")

    print("Índice de Basileia do Banco Central...", flush=True)
    try:
        basel, basel_date = load_basel(dl, today)
    except (requests.RequestException, ValueError, KeyError) as exc:
        basel, basel_date = {}, None
        warnings.append(f"Não consegui baixar o índice de Basileia ({type(exc).__name__}); o critério fica sem dados para bancos.")

    results = [analyze(companies[cnpj], qs, fundamentals.get(cnpj), unit_sizes, ipca, basel, basel_date)
               for cnpj, qs in selected.items()]
    results.sort(key=lambda r: r.ticker)
    errors = [r for r in results if r.status == "erro"]
    if errors:
        warnings.append(f"{plural(len(errors), 'empresa', 'empresas')} sem demonstrações na CVM: "
                        + ", ".join(r.ticker for r in errors) + ".")
    warnings += dl.warnings
    for message in warnings:
        print(f"Aviso: {message}", file=sys.stderr)

    meta = {
        "gerado_em": datetime.now().astimezone().isoformat(timespec="seconds"),
        "ultimo_pregao": last_session,
        "empresas_negociadas": len(by_company),
        "analisadas": len(results) - len(errors),
        "volume_minimo": args.min_volume,
        "pregoes": args.sessions,
        "anos_max": MAX_HISTORY_YEARS,
        "anos_min": MIN_HISTORY_YEARS,
        "limites": {
            "roe": ROE_MIN, "roe_tolerado": ROE_TOLERATED, "margem": MARGIN_MIN, "margem_tolerada": MARGIN_TOLERATED,
            "queda": MAX_DROP_PCT, "divida_ebitda": MAX_NET_DEBT_EBITDA, "roa": ROA_MIN,
            "basileia": BASEL_MIN,
        },
        "ipca": {year: ipca[year] for year in sorted(ipca)[-MAX_HISTORY_YEARS:]},
        "avisos": warnings,
    }
    write_html(results, meta, args.output)

    approved = sum(1 for r in results if r.status == "aprovada")
    marginal = sum(1 for r in results if r.status == "margem")
    print(f"\nHTML gerado: {args.output.resolve()}")
    print(f"Empresas analisadas: {meta['analisadas']} · aprovadas: {approved} · na margem: {marginal} · sem dados: {len(errors)}")
    print(f"Tempo total: {time.time() - start:.1f}s")
    return results


def parse_args(argv: Optional[list[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Screener de qualidade para ações da B3 (dados da CVM e da B3)")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="arquivo HTML de saída (padrão: %(default)s)")
    parser.add_argument("--min-volume", type=float, default=DEFAULT_MIN_VOLUME_BRL,
                        help="volume financeiro médio diário mínimo em R$ (padrão: %(default).0f)")
    parser.add_argument("--sessions", type=int, default=DEFAULT_SESSIONS,
                        help="pregões considerados na média de volume (padrão: %(default)s)")
    parser.add_argument("--tickers", nargs="+", metavar="TICKER", help="analisa só estes tickers, sem filtro de liquidez")
    parser.add_argument("--cache-dir", type=Path, default=DEFAULT_CACHE_DIR, help="pasta do cache de arquivos (padrão: %(default)s)")
    parser.add_argument("--cache-hours", type=float, default=DEFAULT_CACHE_HOURS,
                        help="validade do cache em horas para arquivos que ainda mudam (padrão: %(default)s)")
    parser.add_argument("--refresh", action="store_true", help="baixa tudo de novo, ignorando o cache")
    return parser.parse_args(argv)


def main(argv: Optional[list[str]] = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(errors="replace")  # console do Windows não tem todos os caracteres
        except (AttributeError, ValueError):
            pass
    run(parse_args(argv))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("Interrompido pelo usuário.", file=sys.stderr)
        raise SystemExit(130)
