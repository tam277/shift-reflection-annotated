{-# OPTIONS --rewriting #-}

module DSTrans where

open import DStermK
open import CPSterm

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

-- DS transformation from CPS term to kernel term
dsT : cpstyp → typK
dsT Nat = Nat
dsT (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) = dsT τ₂ ⇒ dsT τ₁ cps[ dsT τ₃ , dsT τ₄ ]

dsContT : conttyp → conttypK
dsContT (K τ₂ ⇒ τ₁) = K dsT τ₂ ▷ dsT τ₁
dsContT (• τ) = • dsT τ

mutual
  dsV : {var : typK → Set} {τ₁ : cpstyp} →
        cpsvalue[ var ∘ dsT ] τ₁ →
        valueK[ var ] (dsT τ₁)
  dsV (CPSVar x) = Var x
  dsV (CPSNum n) = Num n
  dsV (CPSFun e) = Fun (λ x → dsE (e x))
  dsV CPSShift = Shift

  dsE : {var : typK → Set} → {τ : cpstyp} → {Δ : conttyp} →
        cpsterm[ var ∘ dsT , Δ ] τ →
        termK[ var , dsContT Δ ] dsT τ
  dsE (CPSRet k v) = Ret (dsC k) (dsV v)
  dsE (CPSApp v w k) = App (dsV v) (dsV w) (dsC k)
  dsE (CPSShift2 e k) = Shift2 (λ k → dsE (e k)) (dsC k)
  dsE (CPSRetE k e) = RetE (dsC k) (dsE e)

  dsC : {var : typK → Set} → {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
        cpscont[ var ∘ dsT , Δ , τ₁ ] τ₂ →
        pcontextK[ var , dsContT Δ , dsT τ₁ ] dsT τ₂
  dsC CPSKVar = KVar
  dsC CPSKId = KId
  dsC (CPSKLet e) = KLet (λ x → dsE (e x))

-- open import DSterm
-- open import CPSColonTrans
-- test4 = dsV (cpsV𝑐 DSterm.val4)
-- test4' = dsV (cpsV𝑐 DSterm.val4')
{-
Fun (λ x → Ret KVar
 (Fun (λ y → Ret KVar
   (Fun (λ z → Ret KVar
     (Fun (λ w →
       App (Var x) (Var y)
           (KLet (λ x₄ →
             App (Var z) (Var w)
                 (KLet (λ x₅ →
                   App (Var x₄) (Var x₅) KVar)))))))))))
-}

-- test5 = dsV (cpsV𝑐 DSterm.val5)

-- CPS transformation from kernel term to CPS term
cpsT : typK → cpstyp
cpsT Nat = Nat
cpsT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) = cpsT τ₂ ⇒[ cpsT τ₁ ⇒ cpsT τ₃ ]⇒ cpsT τ₄

cpsContT : conttypK → conttyp
cpsContT (K τ₂ ▷ τ₁) = K cpsT τ₂ ⇒ cpsT τ₁
cpsContT (• τ) = • cpsT τ

mutual
  cpsV : {var : cpstyp → Set} {τ₁ : typK} →
         valueK[ var ∘ cpsT ] τ₁ →
         cpsvalue[ var ] cpsT τ₁
  cpsV (Var x) = CPSVar x
  cpsV (Num n) = CPSNum n
  cpsV (Fun e) = CPSFun (λ x → cpsE (e x))
  cpsV Shift = CPSShift

  cpsE : {var : cpstyp → Set} → {τ : typK} → {Δ : conttypK} →
         termK[ var ∘ cpsT , Δ ] τ →
         cpsterm[ var , cpsContT Δ ] cpsT τ
  cpsE (Ret k v) = CPSRet (cpsC k) (cpsV v)
  cpsE (App v w k) = CPSApp (cpsV v) (cpsV w) (cpsC k)
  cpsE (Shift2 e k) = CPSShift2 (λ k → cpsE (e k)) (cpsC k)
  cpsE (RetE k e) = CPSRetE (cpsC k) (cpsE e)

  cpsC : {var : cpstyp → Set} → {τ₁ τ₂ : typK} → {Δ : conttypK} →
         pcontextK[ var ∘ cpsT , Δ , τ₁ ] τ₂ →
         cpscont[ var , cpsContT Δ , cpsT τ₁ ] cpsT τ₂
  cpsC KVar = CPSKVar
  cpsC KId = CPSKId
  cpsC (KLet e) = CPSKLet (λ x → cpsE (e x))

-- for REWRITE
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

cpsT∘dsT≡id : (τ : cpstyp) → cpsT (dsT τ) ≡ τ
cpsT∘dsT≡id Nat = refl
cpsT∘dsT≡id (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
  rewrite cpsT∘dsT≡id τ₁
        | cpsT∘dsT≡id τ₂
        | cpsT∘dsT≡id τ₃
        | cpsT∘dsT≡id τ₄ = refl

{-# REWRITE cpsT∘dsT≡id #-}

cpsContT∘dsContT≡id : (τ : conttyp) → cpsContT (dsContT τ) ≡ τ
cpsContT∘dsContT≡id (K τ₁ ⇒ τ₂) =
  cong₂ K_⇒_ (cpsT∘dsT≡id τ₁) (cpsT∘dsT≡id τ₂)
cpsContT∘dsContT≡id (• τ) =
  cong •_ (cpsT∘dsT≡id τ)

{-# REWRITE cpsContT∘dsContT≡id #-}

dsT∘cpsT≡id : (τ : typK) → dsT (cpsT τ) ≡ τ
dsT∘cpsT≡id Nat = refl
dsT∘cpsT≡id (τ ⇒ τ₁ cps[ τ₂ , τ₃ ])
  rewrite dsT∘cpsT≡id τ
        | dsT∘cpsT≡id τ₁
        | dsT∘cpsT≡id τ₂
        | dsT∘cpsT≡id τ₃ = refl

{-# REWRITE dsT∘cpsT≡id #-}

dsContT∘cpsContT≡id : (τ : conttypK) → dsContT (cpsContT τ) ≡ τ
dsContT∘cpsContT≡id (K τ₁ ▷ τ₂) =
  cong₂ K_▷_ (dsT∘cpsT≡id τ₁) (dsT∘cpsT≡id τ₂)
dsContT∘cpsContT≡id (• τ) = cong •_ (dsT∘cpsT≡id τ)

{-# REWRITE dsContT∘cpsContT≡id #-}
