{-
  ============================================================================
  DS 項と DSKernel 項の間の Reflection (2)  (論文 4 節, 付録 B.2)
  ============================================================================
  DSKernel 言語の項を DS 言語に埋め込んでから A-正規形変換すると、
  元の項に戻ることを示す。論文の 定理 17 にあたる。
    correctV : 任意の値 V について   (V⊙)†† = V
                                     （knormalV (embedV v) ≡ v）
    correct  : 任意の項 MΔ について (MΔ)⊕ :: []Δ = MΔ
                                     （knormal (embed e) KVar ≡ e）
    correctC : 任意の継続 KΔ と DS 言語の項 M について
                                     (KΔ)⊖[M] :: []Δ = M :: KΔ
                                     （knormal (plug (embedC k) e) KVar ≡ knormal e k）
  証明は V, MΔ, KΔ についての相互再帰。

  論文の []Δ にあたるコンテキストは、Δ が k か • かで KVar か KId に分かれる。
  そのため、Agda では Δ = k の場合 (correct, correctC) と、
  Δ = • の場合 (correct2, correctC2) を別々の関数にしている。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect2b where

open import DStermK
open import DSterm
open import Embed

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Extensionality


mutual
  correctV : {var : typK → Set} → {τ₁ : typK} →
              (v : valueK[ var ] τ₁) →
              knormalV (embedV v) ≡ v
  correctV (Var x) = refl
  correctV (Num n) = refl
  correctV (Fun e) =
    cong Fun (extensionality (λ x → correct (e x)))
  correctV Shift = refl

  -- for KVar
  -- Δ = k の場合。[]Δ は []k (KVar)。
  correct : {var : typK → Set} {τ α β : typK} →
            (e : termK[ var , K α ▷ β ] τ) →
            knormal (embed e) KVar ≡ e
  correct (Ret k v) = trans (correctC k _) (cong (Ret k) (correctV v))
  correct (App v w k) = trans (correctC k _)
    (cong₂ (λ v w → App v w k) (correctV v) (correctV w))
  correct (Shift2 v k) = trans (correctC k _)
    (cong₂ Shift2 (extensionality (λ x → correct (v x))) refl)
  correct (RetE k e) = trans (correctC k _) (cong (RetE k) (correct2 e))

  correctC : {var : typK → Set} {τ τ₁ τ₂ α β : typK} →
             (k : pcontextK[ var , K α ▷ β , τ₁ ] τ₂) →
             (e : term[ var ∘ knormalT , embedT τ₁ ▷ embedT τ₂ ] embedT τ) →
             knormal (plug (embedC k) e) KVar ≡ knormal e k
  correctC KVar e = refl
  correctC (KLet e₂) e =
    cong (knormal e) (cong KLet (extensionality (λ x → correct (e₂ x))))

  -- for KId
  -- Δ = • の場合。[]Δ は []• (KId)。
  -- reset の中身 (RetE の e) は • の項なので、correct から correct2 が呼ばれる。
  correct2 : {var : typK → Set} {τ γ : typK}
             (e : termK[ var , • γ ] τ) →
             knormal (embed e) KId ≡ e
  correct2 (Ret k v) = trans (correctC2 k _) (cong (Ret k) (correctV v))
  correct2 (App v w k) = trans (correctC2 k _)
    (cong₂ (λ v w → App v w k) (correctV v) (correctV w))
  correct2 (Shift2 v k) = trans (correctC2 k _)
    (cong₂ Shift2 (extensionality (λ x → correct (v x))) refl)
  correct2 (RetE k e) = trans (correctC2 k _) (cong (RetE k) (correct2 e))

  correctC2 : {var : typK → Set} {τ τ₁ τ₂ γ : typK} →
              (k : pcontextK[ var , • γ , τ₁ ] τ₂) →
              (e : term[ var ∘ knormalT , embedT τ₁ ▷ embedT τ₂ ] embedT τ) →
              knormal (plug (embedC k) e) KId ≡ knormal e k
  correctC2 KId e = refl
  correctC2 (KLet e₂) e =
    cong (knormal e) (cong KLet (extensionality (λ x → correct2 (e₂ x))))
