# shift-reflection

PPL 2023 の論文

> 本田 華歩、山本充子、浅井 健一
> 「shift/resetを含む型付き言語におけるReflection証明」
> 第２５回プログラミングおよびプログラミング言語ワークショップ論文集、
> 20 ページ (2023 年 3 月)。

で行った証明のソースコード。（論文中で記述したものに加え、`Sk.e` の形の
shift が入っても reflection が成り立つことも証明している。）

## ファイル構成

- [README.md](README.md) このファイル
- [Reflect.agda](Reflect.agda) 全体をまとめたファイル
  - [Extensionality.agda](Extensionality.agda) 関数の外延性の公理
  - [DSterm.agda](DSterm.agda) DS 言語
  - [DStermK.agda](DStermK.agda) DSKernel 言語
  - [CPSterm.agda](CPSterm.agda) CPS 言語
  - [Embed.agda](Embed.agda) DS 言語 - DSKernel 言語間の変換
  - [DSTrans.agda](DSTrans.agda) DSKernel 言語 - CPS 言語間の変換
  - [CPSColonTrans.agda](CPSColonTrans.agda) DS 言語 - CPS 言語間の変換
- [Reflect1.agda](Reflect1.agda) Reflection (1) の証明。DS - CPS
  - [Reflect1a.agda](Reflect1a.agda) DS - DSKernel
  - [Reflect1b.agda](Reflect1b.agda) DSKernel - CPS
- [Reflect2.agda](Reflect2.agda) Reflection (2) の証明。CPS - DS
  - [Reflect2a.agda](Reflect2a.agda) CPS - DSKernel
  - [Reflect2b.agda](Reflect2b.agda) DSKernel - DS
- [Reflect3.agda](Reflect3.agda) Reflection (3) の証明。DS → CPS
  - [Reflect3a.agda](Reflect3a.agda) DS → DSKernel
  - [Reflect3b.agda](Reflect3b.agda) DSKernel → CPS
- [Reflect4.agda](Reflect4.agda) Reflection (4) の証明。CPS → DS
  - [Reflect4a.agda](Reflect4a.agda) CPS → DSKernel
  - [Reflect4b.agda](Reflect4b.agda) DSKernel → DS
- [DecomposeColon.agda](DecomposeColon.agda) コロン変換が A-正規形変換と（DSKernel 用の）CPS 変換の合成になることの証明

## 証明環境

- Agda 2.6.2.2
- standard library 1.7
