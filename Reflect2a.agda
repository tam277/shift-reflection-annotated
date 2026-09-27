{-
  ============================================================================
  DSKernel 項と CPS 項の間の Order Isomorphism (2)  (論文 3 節, 付録 A.2)
  ============================================================================
  CPS 言語の項を DS 変換してから CPS 変換すると、元の項に戻ることを示す。
  論文の 定理 8 にあたる。
    correctV  : 任意の値 V について       V♮†′ = V        （cpsV (dsV v) ≡ v）
    correct   : 任意の項 MΔ について     (MΔ)♯° = MΔ     （cpsE (dsE e) ≡ e）
    correctC  : 任意の継続 KΔ について   (KΔ)♭‡ = KΔ     （cpsC (dsC k) ≡ k）
  証明は V, MΔ, KΔ についての相互帰納法。
  Reflect1b.agda と対になっていて、λ 抽象の場合は関数の外延性の公理を使う。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect2a where

open import CPSterm
open import DStermK
open import DSTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Extensionality


mutual
  correctV : {var : typK → Set} → {τ₁ : cpstyp} →
             (v : cpsvalue[ var ∘ dsT ] τ₁) →
             cpsV (dsV v) ≡ v
  correctV (CPSVar x) = refl
  correctV (CPSNum n) = refl
  correctV {var} (CPSFun e) =
    cong CPSFun (extensionality (λ x → correct {var} (e x)))
  correctV CPSShift = refl

  correct : {var : typK → Set} →
            {τ₁ : cpstyp} → {Δ : conttyp} →
            (e : cpsterm[ var ∘ dsT , Δ ] τ₁) →
            cpsE (dsE e) ≡ e
  correct {var} (CPSRet k v) =
    cong₂ CPSRet (correctC {var} k) (correctV {var} v)
  correct {var} (CPSApp v w k)
    rewrite correctV {var} v
          | correctV {var} w
          | correctC {var} k = refl
  correct {var} (CPSShift2 e k) =
    cong₂ CPSShift2 (extensionality (λ x → correct (e x))) (correctC k)
  correct {var} (CPSRetE k e) =
    cong₂ CPSRetE (correctC {var} k) (correct {var} e)

  correctC : {var : typK → Set} →
             {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
             (k : cpscont[ var ∘ dsT , Δ , τ₂ ] τ₁) →
             cpsC (dsC k) ≡ k
  correctC CPSKVar = refl
  correctC CPSKId = refl
  correctC {var} (CPSKLet e) =
    cong CPSKLet (extensionality (λ x → correct {var} (e x)))
