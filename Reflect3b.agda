{-# OPTIONS --rewriting #-}

module Reflect3b where

open import CPSterm
open import DStermK
open import DSTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- substitution lemma
mutual
  lemma-cpsSubstV : {var : cpstyp → Set} {τ₁ τ₂ : typK} →
                    {v : valueK[ var ∘ cpsT ] τ₂} →
                    {v₁ : (var ∘ cpsT) τ₂ → valueK[ var ∘ cpsT ] τ₁} →
                    {v₂ : valueK[ var ∘ cpsT ] τ₁} →
                    (sub : SubstVK v₁ v v₂) →
                    cpsSubstV {var} (λ x → cpsV (v₁ x)) (cpsV v) (cpsV v₂)
  lemma-cpsSubstV sVar= = sVar=
  lemma-cpsSubstV sVar≠ = sVar≠
  lemma-cpsSubstV sNum = sNum
  lemma-cpsSubstV (sFun sub) = sFun (λ x → lemma-cpsSubst (sub x))
  lemma-cpsSubstV sShift = sShift

  lemma-cpsSubst : {var : cpstyp → Set} {τ₁ τ₂ : typK} {Δ : conttypK} →
                   {e : (var ∘ cpsT) τ₂ → termK[ var ∘ cpsT , Δ ] τ₁}
                   {e′ : termK[ var ∘ cpsT , Δ ] τ₁} →
                   {v : valueK[ var ∘ cpsT ] τ₂}
                   (sub : SubstK e v e′) →
                   cpsSubst {var} (λ x → cpsE (e x)) (cpsV v) (cpsE e′)
  lemma-cpsSubst (sRet subC subV) =
    sRet (lemma-cpsSubstC subC) (lemma-cpsSubstV subV)
  lemma-cpsSubst (sApp subV₁ subV₂ subC) =
    sApp (lemma-cpsSubstV subV₁) (lemma-cpsSubstV subV₂) (lemma-cpsSubstC subC)
  lemma-cpsSubst (sShift2 sub subC) =
    sShift2 (λ x → lemma-cpsSubst (sub x)) (lemma-cpsSubstC subC)
  lemma-cpsSubst (sRetE subC sub) =
    sRetE (lemma-cpsSubstC subC) (lemma-cpsSubst sub)

  lemma-cpsSubstC : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typK} {Δ : conttypK} →
                    {v : valueK[ var ∘ cpsT ] τ₂} →
                    {k₁ : (var ∘ cpsT) τ₂ →
                          pcontextK[ var ∘ cpsT , Δ , τ₃ ] τ₁} →
                    {k₂ : pcontextK[ var ∘ cpsT , Δ , τ₃ ] τ₁} →
                    (sub : SubstCK k₁ v k₂) →
                    cpsSubstC {var} (λ x → cpsC (k₁ x)) (cpsV v) (cpsC k₂)
  lemma-cpsSubstC sKVar≠ = sKVar≠
  lemma-cpsSubstC sKId = sKId
  lemma-cpsSubstC (sKLet sub) = sKLet (λ x → lemma-cpsSubst (sub x))

mutual
  lemma-cpsSubst₂ : {var : cpstyp → Set} {τ₁ τ₂ τ₄ : typK} {Δ : conttypK} →
                    {e₁ : termK[ var ∘ cpsT , K τ₂ ▷ τ₄ ] τ₁} →
                    {e′ : termK[ var ∘ cpsT , Δ ] τ₁} →
                    {c : pcontextK[ var ∘ cpsT , Δ , τ₂ ] τ₄} →
                    (sub : SubstK₂ e₁ c e′) →
                    cpsSubst₂ {var} (cpsE e₁) (cpsC c) (cpsE e′)
  lemma-cpsSubst₂ (sRet subC) = sRet (lemma-cpsSubstC₂ subC)
  lemma-cpsSubst₂ (sApp subC) = sApp (lemma-cpsSubstC₂ subC)
  lemma-cpsSubst₂ (sShift2 subC) = sShift2 (lemma-cpsSubstC₂ subC)
  lemma-cpsSubst₂ (sRetE subC) = sRetE (lemma-cpsSubstC₂ subC)

  lemma-cpsSubstC₂ : {var : cpstyp → Set} →
                     {τ₁ τ₂ τ₄ τ₅ : typK} {Δ : conttypK} →
                     {k₁ : pcontextK[ var ∘ cpsT , K τ₂ ▷ τ₄ , τ₅ ] τ₁} →
                     {c : pcontextK[ var ∘ cpsT , Δ , τ₂ ] τ₄} →
                     {k₂ : pcontextK[ var ∘ cpsT , Δ , τ₅ ] τ₁} →
                     (sub : SubstCK₂ k₁ c k₂) →
                     cpsSubstC₂ {var} (cpsC k₁) (cpsC c) (cpsC k₂)
  lemma-cpsSubstC₂ sKVar= = sKVar=
  lemma-cpsSubstC₂ (sKLet sub) = sKLet (λ x → lemma-cpsSubst₂ (sub x))

-- main theorem
mutual
  correctVK : {var : cpstyp → Set} {τ₁ : typK}
              {v v' : valueK[ var ∘ cpsT ] τ₁}
              (red : ReduceVK v v') →
              cpsReduceV {var} (cpsV v) (cpsV v')
  correctVK (REtaV v) = REtaV (cpsV v)
  correctVK (RFun e e' red) =
    RFun (λ x → cpsE (e x)) (λ x → cpsE (e' x)) (λ x → correctK (red x))
  correctVK RId = RId
  correctVK (RTrans red₁ red₂) = RTrans (correctVK red₁) (correctVK red₂)

  correctK : {var : cpstyp → Set} {τ₁ : typK} {Δ : conttypK} →
             {e e′ : termK[ var ∘ cpsT , Δ ] τ₁} →
             ReduceK e e′ →
             cpsReduce {var} (cpsE e) (cpsE e′)
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
  correctK (RShift₂ red) = RShift₂ λ x → correctK (red x)
  correctK (RRetE₁ red) = RRetE₁ (correctCK red)
  correctK (RRetE₂ red) = RRetE₂ (correctK red)
  correctK RId = RId
  correctK (RTrans red₁ red₂) = RTrans (correctK red₁) (correctK red₂)

  correctCK : {var : cpstyp → Set} {τ₁ τ₂ : typK} {Δ : conttypK} →
              {k k' : pcontextK[ var ∘ cpsT , Δ , τ₁ ] τ₂} →
              (red : ReduceCK k k') →
              cpsReduceC {var} (cpsC k) (cpsC k')
  correctCK (REtaLet k) = REtaLet (cpsC k)
  correctCK (RKLet red) = RKLet (λ x → correctK (red x))
  correctCK RId = RId
  correctCK (RTrans red₁ red₂) = RTrans (correctCK red₁) (correctCK red₂)
