{-
  ============================================================================
  DSKernel 項と CPS 項の間の Order Isomorphism (1)  (論文 3 節, 付録 A.1)
  ============================================================================
  DSKernel 言語の項を CPS 変換してから DS 変換すると、元の項に戻ることを示す。
  論文の 定理 7 にあたる。
    correctV  : 任意の値 V について       V   = V†′♮      （dsV (cpsV v) ≡ v）
    correct   : 任意の項 MΔ について     MΔ = (MΔ)°♯     （dsE (cpsE e) ≡ e）
    correctC  : 任意の継続 KΔ について   KΔ = (KΔ)‡♭     （dsC (cpsC k) ≡ k）
  証明は V, MΔ, KΔ についての相互帰納法。
  DSKernel 言語と CPS 言語は一対一に対応しているので、
  簡約 (⟶*) ではなく、等しさ (≡) が成り立つ。

  λ 抽象の場合は、本体が Agda の関数なので、関数の外延性の公理
  (Extensionality.agda) を使って等しさを示している（論文 3 節）。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect1b where

open import CPSterm
open import DStermK
open import DSTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Extensionality


mutual
  correctV : {var : cpstyp → Set} → {τ₁ : typK} →
             (v : valueK[ var ∘ cpsT ] τ₁) →
             dsV (cpsV v) ≡ v

  correctV (Var x) = refl
  correctV (Num n) = refl
  correctV {var} (Fun e) =
    cong Fun (extensionality (λ x → correct {var} (e x)))
  correctV Shift = refl

  correct :  {var : cpstyp → Set} → {τ₁ : typK} → {Δ : conttypK} →
             (e : termK[ var ∘ cpsT , Δ ] τ₁) →
             dsE (cpsE e) ≡ e

  correct {var} (Ret k v) = cong₂ Ret (correctC {var} k) (correctV {var} v)
  correct {var} (App v₁ v₂ k)
    rewrite correctV {var} v₁
          | correctV {var} v₂
          | correctC {var} k  = refl
  correct {var} (Shift2 e k) =
    cong₂ Shift2 (extensionality (λ x → correct (e x))) (correctC k)
  correct {var} (RetE k e) =
    cong₂ RetE (correctC {var} k) (correct {var} e)

  correctC :  {var : cpstyp → Set} → {τ₁ τ₂ : typK} → {Δ : conttypK} →
              (k : pcontextK[ var ∘ cpsT , Δ , τ₂ ] τ₁) →
              dsC (cpsC k) ≡ k

  correctC KVar = refl
  correctC KId = refl
  correctC {var} (KLet e) =
    cong KLet (extensionality (λ x → correct {var} (e x)))
