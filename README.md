# shift-reflection

PPL 2023 の論文

> 本田 華歩、山本充子、浅井 健一
> 「shift/resetを含む型付き言語におけるReflection証明」
> 第２５回プログラミングおよびプログラミング言語ワークショップ論文集、
> 20 ページ (2023 年 3 月)。

で行った証明のソースコード。（論文中で記述したものに加え、`Sk.e` の形の
shift が入っても reflection が成り立つことも証明している。）

---

このリポジトリは、解説コメントを付けたバージョンです。

- 元のコードは、以下のリンクで確認できます。
  http://pllab.is.ocha.ac.jp/~asai/jpapers/ppl/23/
- コメントでは、PPL 2023 の論文を参照しています。
  http://pllab.is.ocha.ac.jp/~asai/jpapers/ppl/23/ppl23.pdf

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

Agda 2.7.0.1（standard library 2.1）でも型検査が通ることを確認済み（2026.09）。

## コメントの記法

コメントは以下の記法で書いています。

- 変換の記号は、論文と同じものを使っています。
  ただし、論文に載っていないコロン変換 (CPSColonTrans.agda) の値の変換は `V†` で表しています。
- 論文の上付き・下付きの記号は、そのまま並べて書いています（論文の $V^{⊙}$ は `V⊙`、$M_Δ$ は `MΔ`）。
- 関数適用は、`@` ではなくスペースで表しています（論文の `V@W` は `V W`）。
- 代入は `[x:=V]` で表しています。
  論文の `[V/x]` と意味は同じで、読みやすさのためにこう書いています。
- 変数名は、次のように使い分けています。
  - 値: `v`、`w`（`v₁`、`v₂` など）
  - 項: `e`（`e₁`、`e₂` など）
  - 継続・コンテキスト: `k`（`k₁`、`k₂` など）。継続の代入で代入する継続は `c`

## HTML で見たい場合

Agda の HTML 出力機能を使うと、色付けされたコードをブラウザで読めます。
コンストラクタや関数の名前をクリックすると、その定義（標準ライブラリを含む）に飛べます。

```bash
agda --html Reflect.agda
```

- `Reflect.agda` から import されているモジュールがすべて型検査され、`html/` ディレクトリに出力されます。
- `html/Reflect.html` をブラウザで開くと、そこから各モジュールをたどれます。
- 出力先は `--html-dir=DIR` で変えられます。
- 型検査が通らないと HTML は出力されません。
- `html/` は各自の手元で生成するものなので、`.gitignore` でコミット対象から外しています。
