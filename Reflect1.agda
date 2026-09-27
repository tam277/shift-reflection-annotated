{-
  ============================================================================
  DS 項と CPS 項の間の Reflection (1)  (論文 5 節, 付録 C)
  ============================================================================
  DS 言語の項を CPS 変換してから DS 変換すると、元の項を簡約したものになる
  (M ⟶* M*#) ことを示す。論文の 系 28 にあたる。
    maincorrectV : 任意の値 V について
                     V ⟶* ((V††)†′)♮⊙
                     （A-正規形変換 → CPS 変換 → DS 変換 → 埋め込み）
    maincorrect  : 任意の DS 言語の項 M と CPS 言語の継続 K について
                     K♭⊖[M] ⟶* (M :: K♭)°♯⊕
  DS 項と DSKernel 項の間の Reflection (1) (Reflect1a.agda, 定理 16) と、
  DSKernel 項と CPS 項の間の Order Isomorphism (1) (Reflect1b.agda, 定理 7) を
  組み合わせて証明する。
  Reflect1b の等式で rewrite して、Reflect1a の結果に帰着させている。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect1 where

open import CPSterm
open import DSterm hiding (conttyp)
open import DStermK
open import DSTrans
open import Embed
open import Reflect1a
open import Reflect1b
open import CPSColonTrans hiding (cpsT)

open import Function
open import Relation.Binary.PropositionalEquality


maincorrectV : {var : typ → Set} {τ₁ β : typ} →
               (v : value[ var ] τ₁) →
               Reduce {β = β} (Val v)
                               (Val (embedV (dsV (cpsV (knormalV v)))))
maincorrectV {var} v
  rewrite Reflect1b.correctV {var ∘ embedT ∘ dsT} (knormalV v) =
  Reflect1a.correctV v

maincorrect : {var : cpstyp → Set} {τ₁ α β : typ} {Δ : conttyp} →
              (e : term[ var ∘ cpsT ∘ knormalT , α ▷ β ] τ₁) →
              (k : cpscont[ var , Δ , cpsT (knormalT α) ] cpsT (knormalT β)) →
              Reduce (plug (embedC (dsC k)) e)
                     (embed (dsE (cpsE (knormal e (dsC k)))))
maincorrect {var} e k rewrite Reflect1b.correct (knormal e (dsC k)) =
  Reflect1a.correct {var ∘ cpsT} e (dsC k)
