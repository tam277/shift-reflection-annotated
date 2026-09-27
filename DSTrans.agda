{-
  ============================================================================
  DSKernel 言語と CPS 言語の間の変換 (論文 3 節, 付録 A)
  ============================================================================
  次の 2 つの変換を定義するファイル。
    ・DS 変換   CPS 言語 → DSKernel 言語   (論文 p.15, 図 10)
    ・CPS 変換  DSKernel 言語 → CPS 言語   (論文 p.16, 図 11)
  DSKernel 言語と CPS 言語は、項・型・簡約規則まで一対一に対応しているので、
  どちらの変換も、コンストラクタを対応するものに置き換えるだけの自明な変換になる（論文 3 節）。
  論文の記法との対応:
    dsV v   : V♮      cpsV v  : V†′   （値）
    dsE e   : M♯      cpsE e  : M°    （項）
    dsC k   : K♭      cpsC k  : K‡    （継続・コンテキスト）
  最後に、型の変換どうしが逆になっていることを示し、REWRITE 規則として登録している。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module DSTrans where

open import DStermK
open import CPSterm

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  DS 変換 (p.15, 図 10)
  ----------------------------------------------------------------------------
  CPS 言語の項を、同じ形の DSKernel 言語の項に変換する。
-}

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
  -- x♮ = x
  dsV (CPSVar x) = Var x
  dsV (CPSNum n) = Num n
  -- (λx.λk.Mk)♮ = λx.(Mk)♯
  dsV (CPSFun e) = Fun (λ x → dsE (e x))
  -- (λw.λj.w (λy.λk.k (j y)) (λx.x))♮ = S
  dsV CPSShift = Shift

  dsE : {var : typK → Set} → {τ : cpstyp} → {Δ : conttyp} →
        cpsterm[ var ∘ dsT , Δ ] τ →
        termK[ var , dsContT Δ ] dsT τ
  -- (KΔ V)♯ = (KΔ)♭[V♮]
  dsE (CPSRet k v) = Ret (dsC k) (dsV v)
  -- (V W KΔ)♯ = (KΔ)♭[V♮ W♮]
  dsE (CPSApp v w k) = App (dsV v) (dsV w) (dsC k)
  -- 論文には無い、Sk.M を CPS 変換したものの場合。
  dsE (CPSShift2 e k) = Shift2 (λ k → dsE (e k)) (dsC k)
  -- (KΔ M•)♯ = (KΔ)♭[<(M•)♯>]
  dsE (CPSRetE k e) = RetE (dsC k) (dsE e)

  dsC : {var : typK → Set} → {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
        cpscont[ var ∘ dsT , Δ , τ₁ ] τ₂ →
        pcontextK[ var , dsContT Δ , dsT τ₁ ] dsT τ₂
  -- k♭ = []k
  dsC CPSKVar = KVar
  -- (λx.x)♭ = []•
  dsC CPSKId = KId
  -- (λx.NΔ)♭ = let x = [] in (NΔ)♯
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

{-
  ----------------------------------------------------------------------------
  CPS 変換 (p.16, 図 11)
  ----------------------------------------------------------------------------
  DSKernel 言語の項を、同じ形の CPS 言語の項に変換する。DS 変換の逆。
-}

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
  -- x†′ = x
  cpsV (Var x) = CPSVar x
  cpsV (Num n) = CPSNum n
  -- (λx.Mk)†′ = λx.λk.(Mk)°
  cpsV (Fun e) = CPSFun (λ x → cpsE (e x))
  -- S†′ = λw.λj.w (λy.λk.k (j y)) (λx.x)
  cpsV Shift = CPSShift

  cpsE : {var : cpstyp → Set} → {τ : typK} → {Δ : conttypK} →
         termK[ var ∘ cpsT , Δ ] τ →
         cpsterm[ var , cpsContT Δ ] cpsT τ
  -- (KΔ[V])° = (KΔ)‡ V†′
  cpsE (Ret k v) = CPSRet (cpsC k) (cpsV v)
  -- (KΔ[V W])° = V†′ W†′ (KΔ)‡
  cpsE (App v w k) = CPSApp (cpsV v) (cpsV w) (cpsC k)
  -- 論文には無い、KΔ[Sk.M] の場合。
  cpsE (Shift2 e k) = CPSShift2 (λ k → cpsE (e k)) (cpsC k)
  -- (KΔ[<M•>])° = (KΔ)‡ (M•)°
  cpsE (RetE k e) = CPSRetE (cpsC k) (cpsE e)

  cpsC : {var : cpstyp → Set} → {τ₁ τ₂ : typK} → {Δ : conttypK} →
         pcontextK[ var ∘ cpsT , Δ , τ₁ ] τ₂ →
         cpscont[ var , cpsContT Δ , cpsT τ₁ ] cpsT τ₂
  -- ([]k)‡ = k
  cpsC KVar = CPSKVar
  -- ([]•)‡ = λx.x
  cpsC KId = CPSKId
  -- (let x = [] in NΔ)‡ = λx.(NΔ)°
  cpsC (KLet e) = CPSKLet (λ x → cpsE (e x))

{-
  ----------------------------------------------------------------------------
  型の変換についての REWRITE 規則
  ----------------------------------------------------------------------------
  cpsT と dsT（継続の型では cpsContT と dsContT）が互いに逆の変換であることを示し、
  REWRITE プラグマで、書き換え規則として登録している。
  登録すると、Agda が型検査のときに cpsT (dsT τ) を自動的に τ に書き換える。
  これにより、変換を組み合わせたときに、型を合わせるための変形を毎回書かずに済む。
  （Embed.agda の REWRITE 規則と同じ考え方。）
-}

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
