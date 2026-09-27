{-
  ============================================================================
  DS 項と CPS 項の間の Reflection (2)  (論文 5 節, 付録 C)
  ============================================================================
  CPS 言語の項を DS 変換してから CPS 変換すると、元の項に戻る
  (N#* = N) ことを示す。論文の 系 29 にあたる。
    maincorrectV  : 任意の値 V について ((V♮⊙)††)†′ = V
                    （DS 変換 → 埋め込み → A-正規形変換 → CPS 変換）
    maincorrect   : 任意の項 NΔ について (NΔ♯⊕ :: []Δ)° = NΔ
                    （NΔ が k を使う項 (Δ = K) の場合。[]Δ は []k）
    maincorrect2  : 同じく、NΔ が恒等継続の下の項 (Δ = •) の場合。[]Δ は []•
  DS 項と DSKernel 項の間の Reflection (2) (Reflect2b.agda, 定理 17) と、
  DSKernel 項と CPS 項の間の Order Isomorphism (2) (Reflect2a.agda, 定理 8) を
  組み合わせて証明する。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect2 where

open import CPSterm
open import DSterm
open import DStermK
open import DSTrans
open import Embed
open import Reflect2a
open import Reflect2b
-- open import Reflect2c
open import CPSColonTrans hiding (cpsT)

open import Function
open import Relation.Binary.PropositionalEquality


maincorrectV : {var : cpstyp → Set} {τ₁ : cpstyp} →
               (v : cpsvalue[ var ] τ₁) →
               cpsV (knormalV (embedV (dsV v))) ≡ v
maincorrectV {var} v rewrite Reflect2b.correctV {var ∘ cpsT} (dsV v) =
  Reflect2a.correctV v

maincorrect : {var : cpstyp → Set} {τ τ₁ τ₂ : cpstyp} →
              (e : cpsterm[ var , K τ₁ ⇒ τ₂ ] τ) →
              cpsE (knormal (embed (dsE e)) KVar) ≡ e
maincorrect {var} e rewrite Reflect2b.correct {var ∘ cpsT} (dsE e) =
  Reflect2a.correct e

maincorrect2 : {var : cpstyp → Set} {τ τ₁ : cpstyp} →
               (e : cpsterm[ var , • τ₁ ] τ) →
               cpsE (knormal (embed (dsE e)) KId) ≡ e
maincorrect2 {var} e rewrite Reflect2b.correct2 {var ∘ cpsT} (dsE e) =
  Reflect2a.correct e
