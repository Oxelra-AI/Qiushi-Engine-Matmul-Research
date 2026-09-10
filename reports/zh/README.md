# 中文研究报告

[阅读 PDF](main.pdf) · [英文定稿](../en/main.pdf) · [LaTeX 主文件](main.tex)

本报告是英文定稿的完整中文译本。正文、证明与三个附录逐节对应；
摘要按中文阅读习惯组织为连贯的一段，先交代问题背景，再说明证明机制与研究价值。
不增补研究结论，不删减重要纠错或适用条件。公式标签、参考文献及
作者顺序与英文稿一致；图示沿用英文原图，图注译为中文。

`main.tex` 是唯一主文件，研究历程与同期工作比较均收入同一 PDF。
`latex/`、`sections/`、`figures/` 和 `refs.bib` 构成自包含的 XeLaTeX 工程。
基础样式、参考文献、标识和图示源码与英文版保持一致，由测试检查。
作者栏采用“中文名（英文名）”，按四行四列排布；作者顺序、英文姓名、
通讯作者与邮箱均与英文版一致，单位名称及通讯说明译为中文。
中文排版在此基础上单独设置：正文首行统一缩进两个汉字，标题后首段同样缩进，
行距按中文阅读需要调整；图表、列表及定理环境保留各自的规范格式。
中文使用 CTeX 与公开的 Noto CJK 字体，延续 Qiushi 中文报告的字体选择。
在 Ubuntu/Debian 上，相应依赖为 `texlive-lang-chinese` 和 `fonts-noto-cjk`；
不依赖私有字体或研究系统。

在仓库根目录运行：

```bash
make reports-zh
make source-zh
```

完整编译命令也可在本目录运行：

```bash
latexmk -xelatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

源码 ZIP 输出到 `dist/report-sources/qiushi-matmul-zh-source.zip`。
中文 PDF 不替代英文投稿稿件；数学证书与复现入口仍见
[复现说明](../../reproducibility/README.md)。
