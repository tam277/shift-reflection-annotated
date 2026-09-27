{-
  ============================================================================
  DSKernel 項と CPS 項の間の Order Isomorphism (3)  (論文 3 節, 付録 A.3)
  ============================================================================
  DSKernel 言語の簡約が、CPS 変換した後の CPS 言語の簡約で保たれることを示す。
  論文の 定理 11 にあたる。
    correctVK : 任意の値 V, W について       V ⟶* W ならば V†′ ⟶* W†′
    correctK  : 任意の項 M, N について       M ⟶* N ならば M° ⟶* N°
    correctCK : 任意の継続 JΔ, KΔ について JΔ ⟶* KΔ ならば (JΔ)‡ ⟶* (KΔ)‡
  DSKernel 言語と CPS 言語の簡約規則は一対一に対応しているので、
  各簡約規則を、対応する CPS 言語の簡約規則に置き換えるだけで証明できる。
  そのために、まず代入補題を示している。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect3b where

open import CPSterm
open import DStermK
open import DSTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  値の代入補題 (論文 補題 9)
  ----------------------------------------------------------------------------
  代入してから CPS 変換しても、CPS 変換してから代入しても同じになる。
    lemma-cpsSubstV : (W[x:=V])†′ = W†′[x:=V†′]
    lemma-cpsSubst  : (M[x:=V])° = M°[x:=V†′]
    lemma-cpsSubstC : (KΔ[x:=V])‡ = (KΔ)‡[x:=V†′]
  いずれも代入関係として述べていて、証明は代入関係についての相互帰納法。
-}

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

{-
  ----------------------------------------------------------------------------
  継続の代入補題 (論文 補題 10)
  ----------------------------------------------------------------------------
    lemma-cpsSubst₂  : (Mk[k:=JΔ])° = (Mk)°[k:=(JΔ)‡]
    lemma-cpsSubstC₂ : (Kk[k:=JΔ])‡ = (Kk)‡[k:=(JΔ)‡]
  継続の代入では値は変化しないので、項とコンテキストだけの相互再帰になる（論文 p.17）。
-}

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

{-
  ----------------------------------------------------------------------------
  主定理 (論文 定理 11)
  ----------------------------------------------------------------------------
  簡約 ReduceVK, ReduceK, ReduceCK についての相互帰納法。
  各簡約規則を、CPSterm.agda の同じ名前の簡約規則に置き換えている。
-}

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
