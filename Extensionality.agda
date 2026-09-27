{-
  ============================================================================
  関数の外延性の公理 (論文 1.2 節, 3 節, 4 節)
  ============================================================================
  「すべての引数 x について f x ≡ g x ならば f ≡ g」という公理を仮定する。
  Agda ではこれを証明できないので、postulate で仮定している。

  PHOAS では λ 抽象の本体が Agda の関数で表されるため、
  λ 抽象どうしが等しいことを言うには、関数の等しさが必要になる。
  （論文 3 節の最後の段落を参照。）
  Extensionality a b は、標準ライブラリで次のように定義されている型。
    ∀ {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
      (∀ x → f x ≡ g x) → f ≡ g
  ============================================================================
-}

module Extensionality where

open import Level using (Level)
open import Axiom.Extensionality.Propositional

postulate
  extensionality : {a b : Level} → Extensionality a b
