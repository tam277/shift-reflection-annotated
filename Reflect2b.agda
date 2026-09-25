{-# OPTIONS --rewriting #-}

module Reflect2b where

open import DStermK
open import DSterm
open import Embed

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Extensionality

-- main theorem

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
