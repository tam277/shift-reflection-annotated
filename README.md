# shift-reflection

PPL 2023 の論文

> 本田 華歩、山本 充子、浅井 健一
> 「shift/resetを含む型付き言語におけるReflection証明」
> 第２５回プログラミングおよびプログラミング言語ワークショップ論文集、
> 20 ページ (2023 年 3 月)。

で行った証明のソースコード。（論文中で記述したものに加え、`Sk.e` の形の
shift が入っても reflection が成り立つことも証明している。）

## ファイル構成

| ファイル | 内容 |
| --- | --- |
| `README.md` | このファイル |
| `Reflect.agda` | 全体をまとめたファイル |
| &emsp;`Extensionality.agda` | 関数の外延性の公理 |
| &emsp;`DSterm.agda` | DS 言語 |
| &emsp;`DStermK.agda` | DSKernel 言語 |
| &emsp;`CPSterm.agda` | CPS 言語 |
| &emsp;`Embed.agda` | DS 言語 - DSKernel 言語間の変換 |
| &emsp;`DSTrans.agda` | DSKernel 言語 - CPS 言語間の変換 |
| &emsp;`CPSColonTrans.agda` | DS 言語 - CPS 言語間の変換 |
| `Reflect1.agda` | Reflection (1) の証明。DS - CPS |
| &emsp;`Reflect1a.agda` | DS - DSKernel |
| &emsp;`Reflect1b.agda` | DSKernel - CPS |
| `Reflect2.agda` | Reflection (2) の証明。CPS - DS |
| &emsp;`Reflect2a.agda` | CPS - DSKernel |
| &emsp;`Reflect2b.agda` | DSKernel - DS |
| `Reflect3.agda` | Reflection (3) の証明。DS → CPS |
| &emsp;`Reflect3a.agda` | DS → DSKernel |
| &emsp;`Reflect3b.agda` | DSKernel → CPS |
| `Reflect4.agda` | Reflection (4) の証明。CPS → DS |
| &emsp;`Reflect4a.agda` | CPS → DSKernel |
| &emsp;`Reflect4b.agda` | DSKernel → DS |
| `DecomposeColon.agda` | コロン変換が A-正規形変換と（DSKernel 用の）CPS 変換の合成になることの証明 |

## 証明環境

- Agda 2.6.2.2
- standard library 1.7
