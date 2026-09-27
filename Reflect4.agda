{-
  ============================================================================
  DS 項と CPS 項の間の Reflection (4)  (論文 5 節, 付録 C)
  ============================================================================
  CPS 言語の簡約が、DS 変換した後の DS 言語の簡約で保たれる
  (N ⟶ N′ ならば N# ⟶* N′#) ことを示す。論文の 系 31 にあたる。
    correctV  : 任意の値 V, W について       V ⟶* W ならば V♮⊙ ⟶* W♮⊙
    correct   : 任意の項 MΔ, NΔ について   MΔ ⟶* NΔ ならば (MΔ)♯⊕ ⟶* (NΔ)♯⊕
    correctC  : 任意の継続 JΔ, KΔ について JΔ ⟶* KΔ ならば、
                任意の DS 言語の項 M について (JΔ)♭⊖[M] ⟶* (KΔ)♭⊖[M]
  DSKernel 項と CPS 項の間の Order Isomorphism (4) (Reflect4a.agda, 定理 14) と、
  DS 項と DSKernel 項の間の Reflection (4) (Reflect4b.agda, 定理 27) を
  そのまま合成している。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect4 where

open import CPSterm
open import DStermK
open import DSterm
open import DSTrans
open import Embed
open import Reflect4a
open import Reflect4b

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

correctV : {var : typ → Set} {τ₁ : cpstyp} {τ : typ} →
           {v v′ : cpsvalue[ var ∘ embedT ∘ dsT ] τ₁} →
           cpsReduceV v v′ →
           Reduce {var} {τ} (Val (embedV (dsV v))) (Val (embedV (dsV v′)))
correctV red = correctVE (correctVK red)

correct : {var : typ → Set} {τ₁ : cpstyp} {Δ : CPSterm.conttyp} →
          {e e′ : cpsterm[ var ∘ embedT ∘ dsT , Δ ] τ₁} →
          cpsReduce e e′ →
          Reduce {var} (embed (dsE e)) (embed (dsE e′))
correct red = correctE (correctK red)

correctC : {var : typ → Set} {τ₃ τ₄ τ₅ : cpstyp} {Δ : CPSterm.conttyp} →
           {k k′ : cpscont[ var ∘ embedT ∘ dsT , Δ , τ₃ ] τ₄} →
           cpsReduceC k k′ →
           {e : term[ var , embedT (dsT τ₃) ▷ embedT (dsT τ₄) ]
                    embedT (dsT τ₅)} →
           Reduce {var} (plug (embedC (dsC k)) e)
                        (plug (embedC (dsC k′)) e)
correctC {τ₅ = τ₅} red = correctCE {τ₅ = dsT τ₅} (correctCK red)
