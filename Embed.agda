{-# OPTIONS --rewriting #-}

module Embed where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import DStermK
open import DSterm

-- Embedding kernel term to source term

embedT : typK → typ
embedT Nat = Nat
embedT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  embedT τ₂ ⇒ embedT τ₁ cps[ embedT τ₃ , embedT τ₄ ]

embedContT : conttypK → conttyp
embedContT (K τ₁ ▷ τ₂) = embedT τ₁ ▷ embedT τ₂
embedContT (• τ) = embedT τ ▷ embedT τ

mutual
  embedV : {var : typ → Set} {τ : typK} →
           valueK[ var ∘ embedT ] τ →
           value[ var ] embedT τ
  embedV (Var x) = Var x
  embedV (Num n) = Num n
  embedV (Fun e) = Fun (λ x → embed (e x))
  embedV Shift = Shift

  embed : {var : typ → Set} {τ : typK} {Δ : conttypK} →
          termK[ var ∘ embedT , Δ ] τ →
          term[ var , embedContT Δ ] embedT τ
  embed (Ret k v) =
    plug (embedC k) (Val (embedV v))
  embed (App v w k) =
    plug (embedC k)
         (NonVal (App (Val (embedV v)) (Val (embedV w))))
  embed (Shift2 e k) =
    plug (embedC k)
         (NonVal (Shift2 (λ k → embed (e k))))
  embed (RetE {τ} k e) =
    plug (embedC k) (NonVal (Reset (embed e)))

  embedC : {var : typ → Set} {τ₃ τ₄ : typK} {Δ : conttypK} →
           pcontextK[ var ∘ embedT , Δ , τ₃ ] τ₄ →
           pcontext[ var , embedContT Δ , embedT τ₃ ] embedT τ₄
  embedC KVar = Hole
  embedC KId = Hole
  embedC {Δ = K τ₁ ▷ τ₂} (KLet e) = Let Hole (λ x → embed (e x))
  embedC {Δ = • τ} (KLet e) = Let Hole (λ x → embed (e x))

-- λxyzw. (x y) (z w)
{- DSterm:
Fun (λ x → Val (Fun (λ y → Val (Fun (λ z → Val (Fun (λ w →
  NonVal (App (NonVal (App (Val (Var x)) (Val (Var y))))
              (NonVal (App (Val (Var z)) (Val (Var w))))))))))))
-}

{- K-normal form of the above expression in DS
Fun (λ x → Val (Fun (λ y → Val (Fun (λ z → Val (Fun (λ w →
  NonVal (Let (NonVal (App (Val (Var x)) (Val (Var y)))) (λ m →
    NonVal (Let (NonVal (App (Val (Var z)) (Val (Var w)))) (λ n →
      NonVal (App (Val (Var m)) (Val (Var n))))))))))))))
-}

{- DSterm of the above expression using plug
Fun (λ x → Val (Fun (λ y → Val (Fun (λ z → Val (Fun (λ w →
  proj₂ (plug (Let Hole (λ m →
          proj₂ (plug (Let Hole (λ n →
                  proj₂ (plug Hole
                          (NonVal (App (Val (Var m)) (Val (Var n)))))))
            (NonVal (App (Val (Var z)) (Val (Var w)))))))
    (NonVal (App (Val (Var x)) (Val (Var y))))))))))))
-}

{- DStermK, KNormal:
Fun (λ x → Ret KVar
  (Fun (λ y → Ret KVar
    (Fun (λ z → Ret KVar
      (Fun (λ w →
        App (Var x) (Var y)
            (KLet (λ m →
              App (Var z) (Var w)
                  (KLet (λ n → App (Var m) (Var n) KVar)))))))))))
-}

{- CPSterm:
CPSFun (λ x → CPSRet CPSKVar
  (CPSFun (λ y → CPSRet CPSKVar
    (CPSFun (λ z → CPSRet CPSKVar
      (CPSFun (λ w →
        CPSApp (CPSVar x) (CPSVar y)
               (CPSKLet (λ m →
                 CPSApp (CPSVar z) (CPSVar w)
                        (CPSKLet (λ n →
                          CPSApp (CPSVar m) (CPSVar n) CPSKVar)))))))))))
-}

-- λx.λy.y ((λz.z) x)
{- DSterm:
Fun (λ x → Val (Fun (λ y →
  NonVal (App (Val (Var y))
              (NonVal (App (Val (Fun (λ z → Val (Var z))))
                           (Val (Var x))))))))
-}

{- CPSterm:
CPSFun
(λ x → CPSRet CPSKVar (CPSFun (λ y →
  CPSApp (CPSFun (λ z → CPSRet CPSKVar (CPSVar z))) (CPSVar x)
         (CPSKLet (λ n → CPSApp (CPSVar y) (CPSVar n) CPSKVar)))))
-}

{- DStermK:
Fun (λ x → Ret KVar (Fun (λ y →
  App (Fun (λ z → Ret KVar (Var Z))) (Var x)
      (KLet (λ n → App (Var y) (Var n) KVar)))))
-}

-- open import DSTrans
-- open import CPSColonTrans
-- test5 = embedV (dsV (cpsV𝑐 DSterm.val5))

{- DSterm after embedding:
Fun (λ x → Val (Fun (λ y →
  NonVal (Let (NonVal (App (Val (Fun (λ z → Val (Var z)))) (Val (Var x))))
              (λ n → NonVal (App (Val (Var y)) (Val (Var n))))))))
-}

-- K-normal transformation to kernel term

knormalT : typ → typK
knormalT Nat = Nat
knormalT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  knormalT τ₂ ⇒ knormalT τ₁ cps[ knormalT τ₃ , knormalT τ₄ ]

knormalContT : conttyp → conttypK
knormalContT (τ₁ ▷ τ₂) = K knormalT τ₁ ▷ knormalT τ₂

mutual
  -- value
  knormalV : {var : typK → Set} → {τ₁ : typ} →
             value[ var ∘ knormalT ] τ₁ →
             valueK[ var ] knormalT τ₁
  knormalV (Var x) = Var x
  knormalV (Num n) = Num n
  knormalV (Fun e) = Fun (λ x → knormal (e x) KVar)
  knormalV Shift = Shift

  -- term
  knormal : {var : typK → Set} →
            {τ₁ τ₂ τ₃ : typ} → {Δ : conttypK} →
            term[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃ →
            pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂ →
            termK[ var , Δ ] (knormalT τ₃)

  -- V : K
  knormal (Val v) k = Ret k (knormalV v)

  -- P Q : K
  knormal (NonVal (App (NonVal e₁) (NonVal e₂))) k =
    knormal (NonVal e₁) (KLet (λ m →
      knormal (NonVal e₂) (KLet (λ n →
        App (Var m) (Var n) k))))

  -- P W : K
  knormal (NonVal (App (NonVal e₁) (Val v₂))) k =
    knormal (NonVal e₁) (KLet (λ m →
      App (Var m) (knormalV v₂) k))

  -- V Q : K
  knormal (NonVal (App (Val v₁) (NonVal e₂))) k =
    knormal (NonVal e₂) (KLet (λ n →
      App (knormalV v₁) (Var n) k))

  -- V W : K
  knormal (NonVal (App (Val v₁) (Val v₂))) k =
    App (knormalV v₁) (knormalV v₂) k

  -- Sk.M : K
  knormal (NonVal (Shift2 e)) k =
    Shift2 (λ k → knormal (e k) KVar) k

  -- ⟨ M ⟩ : K
  knormal (NonVal (Reset e)) k =
    RetE k (knormal e KId)

  -- let x = M in N : K
  knormal (NonVal (Let e₁ e₂)) k =
    knormal e₁ (KLet (λ m →
      knormal (e₂ m) k))

-- examples
test1 : {var : typK → Set} → {τ₁ τ₂ : typ} →
        valueK[ var ] (knormalT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test1 = knormalV DSterm.val1
-- Fun (λ x → Ret KVar (Var x))

test2 : {var : typK → Set} → {τ₁ τ₂ : typ} →
        valueK[ var ] (knormalT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test2 = knormalV DSterm.val2
-- Fun (λ x → App Shift (Fun (λ x₁ → App (Var x₁) (Var x) KVar)) KVar)

test3 : {var : typK → Set} → {τ₁ τ₂ τ₃ τ : typ} →
        valueK[ var ] (knormalT (τ₁ ⇒ τ₂ cps[ τ₃ , τ₁ ]))
test3 {τ = τ} = knormalV (DSterm.val3 {τ = τ})
-- λ {τ} → Fun (λ x → App Shift (Fun (λ x₁ → Ret KVar (Var x))) KVar)

-- for REWRITE
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

knormalT∘embedT≡id : (τ : typK) → knormalT (embedT τ) ≡ τ
knormalT∘embedT≡id Nat = refl
knormalT∘embedT≡id (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])
  rewrite knormalT∘embedT≡id τ₁
        | knormalT∘embedT≡id τ₂
        | knormalT∘embedT≡id τ₃
        | knormalT∘embedT≡id τ₄ = refl

{-# REWRITE knormalT∘embedT≡id #-}

embedT∘knormalT≡id : (τ : typ) → embedT (knormalT τ) ≡ τ
embedT∘knormalT≡id Nat = refl
embedT∘knormalT≡id (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])
  rewrite embedT∘knormalT≡id τ₁
        | embedT∘knormalT≡id τ₂
        | embedT∘knormalT≡id τ₃
        | embedT∘knormalT≡id τ₄ = refl

embedContT∘knormalContT≡id : (Δ : conttyp) → embedContT (knormalContT Δ) ≡ Δ
embedContT∘knormalContT≡id (τ₁ ▷ τ₂)
  rewrite embedT∘knormalT≡id τ₁
        | embedT∘knormalT≡id τ₂ = refl

{-# REWRITE embedT∘knormalT≡id #-}

-- examples

-- test4 = knormalV DSterm.val4
-- test4' = knormalV DSterm.val4'
{-
Fun (λ x → Ret KVar
  (Fun (λ y → Ret KVar
    (Fun (λ z → Ret KVar
      (Fun (λ w →
        App (Var x) (Var y)
            (KLet (λ m →
              App (Var z) (Var w)
                  (KLet (λ n → App (Var m) (Var n) KVar)))))))))))
-}

{-
-- lemma
colon₂ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {Δ : conttyp} →
         (v₁ : value[ var ∘ cpsT ] τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) →
         (e₂ : term[ var ∘ cpsT ] τ₄ cps[ τ₅ , τ₃ ]) →
         (k : cpscont[ var , Δ ] cpsT τ₁ ⇒ cpsT τ₂) →
         cpsReduce (cpsE𝑐 e₂ (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
                   (cpsE𝑐 (NonVal (App (Val v₁) e₂)) k)
colon₂ v₁ (Val v₂) k = begin
    (cpsE𝑐 (Val v₂) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
  ≡⟨ refl ⟩
    (CPSRet (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)) (cpsV𝑐 v₂))
  ⟶⟨ RBetaLet (sApp (cpsSubstV≠ (cpsV𝑐 v₁)) sVar= (cpsSubstC≠ k)) ⟩
    (CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k)
  ≡⟨ refl ⟩
    (cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k)
  ∎ where open CPSterm.Reasoning
colon₂ v₁ (NonVal e₂) k = RId
-}
