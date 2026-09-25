{-# OPTIONS --rewriting #-}

module Reflect1b where

open import CPSterm
open import DStermK
open import DSTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Extensionality

-- main theorem

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
