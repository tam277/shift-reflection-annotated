{-# OPTIONS --rewriting #-}

module Reflect4a where

open import CPSterm
open import DStermK
open import DSTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- substitution lemma
mutual
  lemma-cpsSubstV : {var : typK → Set} {τ₁ τ₂ : cpstyp} →
                    {v : cpsvalue[ var ∘ dsT ] τ₂} →
                    {v₁ : (var ∘ dsT) τ₂ → cpsvalue[ var ∘ dsT ] τ₁} →
                    {v₂ : cpsvalue[ var ∘ dsT ] τ₁} →
                    (sub : cpsSubstV v₁ v v₂) →
                    SubstVK {var} (λ x → dsV (v₁ x)) (dsV v) (dsV v₂)
  lemma-cpsSubstV sVar= = sVar=
  lemma-cpsSubstV sVar≠ = sVar≠
  lemma-cpsSubstV sNum = sNum
  lemma-cpsSubstV {var} (sFun sub) = sFun (λ x → lemma-cpsSubst (sub x))
  lemma-cpsSubstV sShift = sShift

  lemma-cpsSubst : {var : typK → Set} {τ₁ τ₂ : cpstyp} {Δ : conttyp} →
                   {e : (var ∘ dsT) τ₂ → cpsterm[ var ∘ dsT , Δ ] τ₁}
                   {e′ : cpsterm[ var ∘ dsT , Δ ] τ₁} →
                   {v : cpsvalue[ var ∘ dsT ] τ₂}
                   (sub : cpsSubst e v e′) →
                   SubstK {var} (λ x → dsE (e x)) (dsV v) (dsE e′)
  lemma-cpsSubst (sRet subK subV) =
    sRet (lemma-cpsSubstC subK) (lemma-cpsSubstV subV)
  lemma-cpsSubst (sApp subV₁ subV₂ subC) =
    sApp (lemma-cpsSubstV subV₁) (lemma-cpsSubstV subV₂) (lemma-cpsSubstC subC)
  lemma-cpsSubst (sShift2 subC subK) =
    sShift2 (λ x → lemma-cpsSubst (subC x)) (lemma-cpsSubstC subK)
  lemma-cpsSubst (sRetE subC sub) =
    sRetE (lemma-cpsSubstC subC) (lemma-cpsSubst sub)

  lemma-cpsSubstC : {var : typK → Set} {τ₁ τ₂ τ₃ : cpstyp} {Δ : conttyp} →
                    {v : cpsvalue[ var ∘ dsT ] τ₂} →
                    {k₁ : (var ∘ dsT) τ₂ →
                          cpscont[ var ∘ dsT , Δ , τ₃ ] τ₁} →
                    {k₂ : cpscont[ var ∘ dsT , Δ , τ₃ ] τ₁} →
                    (sub : cpsSubstC k₁ v k₂) →
                    SubstCK {var} (λ x → dsC (k₁ x)) (dsV v) (dsC k₂)
  lemma-cpsSubstC sKVar≠ = sKVar≠
  lemma-cpsSubstC sKId = sKId
  lemma-cpsSubstC (sKLet sub) = sKLet (λ x → lemma-cpsSubst (sub x))

mutual
  lemma-cpsSubst₂ : {var : typK → Set} {τ₁ τ₂ τ₄ : cpstyp} {Δ : conttyp} →
                    {e₁ : cpsterm[ var ∘ dsT , K τ₂ ⇒ τ₄ ] τ₁} →
                    {e′ : cpsterm[ var ∘ dsT , Δ ] τ₁} →
                    {c : cpscont[ var ∘ dsT , Δ , τ₂ ] τ₄} →
                    (sub : cpsSubst₂ e₁ c e′) →
                    SubstK₂ {var} (dsE e₁) (dsC c) (dsE e′)
  lemma-cpsSubst₂ (sRet subC) = sRet (lemma-cpsSubstC₂ subC)
  lemma-cpsSubst₂ (sApp subC) = sApp (lemma-cpsSubstC₂ subC)
  lemma-cpsSubst₂ (sShift2 subC) = sShift2 (lemma-cpsSubstC₂ subC)
  lemma-cpsSubst₂ (sRetE subC) = sRetE (lemma-cpsSubstC₂ subC)

  lemma-cpsSubstC₂ : {var : typK → Set} →
                     {τ₁ τ₂ τ₄ τ₅ : cpstyp} {Δ : conttyp} →
                     {k₁ : cpscont[ var ∘ dsT , K τ₂ ⇒ τ₄ , τ₅ ] τ₁} →
                     {c : cpscont[ var ∘ dsT , Δ , τ₂ ] τ₄} →
                     {k₂ : cpscont[ var ∘ dsT , Δ , τ₅ ] τ₁} →
                     (sub : cpsSubstC₂ k₁ c k₂) →
                     SubstCK₂ {var} (dsC k₁) (dsC c) (dsC k₂)
  lemma-cpsSubstC₂ sKVar= = sKVar=
  lemma-cpsSubstC₂ (sKLet sub) = sKLet (λ x → lemma-cpsSubst₂ (sub x))

-- main theorem
mutual
  correctVK : {var : typK → Set} {τ₁ : cpstyp}
              {v v' : cpsvalue[ var ∘ dsT ] τ₁}
              (red : cpsReduceV v v') →
              ReduceVK {var} (dsV v) (dsV v')
  correctVK (REtaV v) = REtaV (dsV v)
  correctVK (RFun e e' red) =
    RFun (λ x → dsE (e x)) (λ x → dsE (e' x)) (λ x → correctK (red x))
  correctVK RId = RId
  correctVK (RTrans red₁ red₂) = RTrans (correctVK red₁) (correctVK red₂)

  correctK : {var : typK → Set} {τ₁ : cpstyp} {Δ : conttyp} →
             {e e′ : cpsterm[ var ∘ dsT , Δ ] τ₁} →
             cpsReduce e e′ →
             ReduceK {var} (dsE e) (dsE e′)
  correctK (RBetaV sub subK) =
    RBetaV (lemma-cpsSubst sub) (lemma-cpsSubst₂ subK)
  correctK (RBetaLet sub) = RBetaLet (lemma-cpsSubst sub)
  correctK RShift = RShift
  correctK RShift2 = RShift2
  correctK RReset = RReset
  correctK (RRet₁ red) = RRet₁ (correctCK red)
  correctK (RRet₂ red) = RRet₂ (correctVK red)
  correctK (RApp₁ red) = RApp₁ (correctVK red)
  correctK (RApp₂ red) = RApp₂ (correctVK red)
  correctK (RApp₃ red) = RApp₃ (correctCK red)
  correctK (RShift₁ red) = RShift₁ (correctCK red)
  correctK (RShift₂ red) = RShift₂ (λ x → correctK (red x))
  correctK (RRetE₁ red) = RRetE₁ (correctCK red)
  correctK (RRetE₂ red) = RRetE₂ (correctK red)
  correctK RId = RId
  correctK (RTrans red₁ red₂) = RTrans (correctK red₁) (correctK red₂)

  correctCK : {var : typK → Set} {τ₁ τ₂ : cpstyp} {Δ : conttyp} →
              {k k' : cpscont[ var ∘ dsT , Δ , τ₁ ] τ₂} →
              (red : cpsReduceC k k') →
              ReduceCK {var} (dsC k) (dsC k')
  correctCK (REtaLet k) = REtaLet (dsC k)
  correctCK (RKLet red) = RKLet (λ x → correctK (red x))
  correctCK RId = RId
  correctCK (RTrans red₁ red₂) = RTrans (correctCK red₁) (correctCK red₂)
