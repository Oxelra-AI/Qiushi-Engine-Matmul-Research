# 含 Lean 形式化的研究报告

[中文 PDF](main.pdf) | [英文版](../en-lean/main.pdf) | [LaTeX 主文件](main.tex)

本版将已完成的 Lean 证明融入结构性论证、计算验证与研究历程，保留原始数学
论证、作者、参考文献和图表，并使命题条件与形式化证明准确对应。

`main.tex` 是唯一主文件，包含全部三个附录。`latex/`、`sections/`、`figures/`
和 `refs.bib` 构成自包含的 XeLaTeX 工程；中文排版使用原版的 Noto CJK 字体。
在本目录内编译：

```sh
latexmk -xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

[形式化覆盖表](../../formalization/COVERAGE.md) 记录精确命题与假设；
[Lean 指南](../../formalization/README.md) 说明证明复现方法。
Lean 整数分支证书与原始 CNF/DRAT 材料是不同的验证路线。

本版独立于[原始中文报告](../zh/main.pdf)，其构建凭据为
[lean-report-build.json](../../evidence/lean-report-build.json)。
