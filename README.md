# Screener de qualidade · B3

Filtra as ações da B3 por um método de qualidade e publica o resultado numa página, atualizada toda segunda-feira.

**Critérios** (últimos 5 exercícios): ROE acima de 15%, margem líquida acima de 15%, dívida líquida abaixo de 3x o EBITDA, receita e lucro crescentes em valores corrigidos pelo IPCA. Bancos usam métricas equivalentes (ROA, índice de Basileia, resultado da intermediação); seguradoras e holdings, só ROE e lucro.

**Resultado:** "Aprovado" cumpre tudo à risca; "Aprovado com Ressalvas" usa a tolerância em algum critério (alguns anos de ROE ou margem entre 10% e 15%, ou pequenas quedas de receita ou lucro) ou tem algum alerta alto na qualidade do lucro. Clicando numa empresa, a página mostra a evolução de cada critério ano a ano, os alertas de qualidade do lucro e os links para a CVM.

**Dados oficiais e públicos:** demonstrações financeiras da CVM, cotações da B3, IPCA e índice de Basileia do Banco Central.

## Como funciona a atualização

O GitHub Actions (`.github/workflows/screener.yml`) roda o script toda segunda às 7h (horário de Brasília) e publica o HTML no GitHub Pages. Para atualizar na hora: aba **Actions** → **Screener semanal** → **Run workflow**.

## Rodar no computador

```bash
pip install -r requirements.txt
python b3_screener.py
```

Gera `b3_screener.html`. A primeira execução baixa cerca de 90 MB; as seguintes usam o cache em `.b3_cache/`. Opções: `python b3_screener.py --help`.

## Limitações

É um primeiro filtro, não recomendação de investimento. A CVM não marca itens não recorrentes, e o número de ações de algumas empresas pequenas vem desatualizado (o valuation aparece com ⚠ quando isso é detectado). Os alertas de qualidade do lucro indicam onde ler as notas explicativas com cuidado.
