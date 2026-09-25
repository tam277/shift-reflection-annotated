module CPSColonTrans where

open import Data.Product
open import DSterm hiding (conttyp)
open import CPSterm
open import Function
open import Relation.Binary.PropositionalEquality

-- CPS transformation

cpsT : typ → cpstyp
cpsT Nat     = Nat
cpsT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  cpsT τ₂ ⇒[ cpsT τ₁ ⇒ cpsT τ₃ ]⇒ cpsT τ₄

-- CPS transformation to target term
mutual
  -- value
  cpsV𝑐 : {var : cpstyp → Set} → {τ₁ : typ} →
          value[ var ∘ cpsT ] τ₁ →
          cpsvalue[ var ] (cpsT τ₁)
  cpsV𝑐 (Var x) = CPSVar x
  cpsV𝑐 (Num n) = CPSNum n
  cpsV𝑐 (Fun e) = CPSFun (λ x → cpsE𝑐 (e x) CPSKVar)
  cpsV𝑐 Shift = CPSShift

  -- term
  cpsE𝑐 : {var : cpstyp → Set} →
          {τ₁ τ₂ τ₃ : typ} → {Δ : conttyp} →
          term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃ →
          cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂ →
          cpsterm[ var , Δ ] (cpsT τ₃)

  -- V : K
  cpsE𝑐 (Val v) k = CPSRet k (cpsV𝑐 v)

  -- P Q : K
  cpsE𝑐 (NonVal (App (NonVal e₁) (NonVal e₂))) k =
    cpsE𝑐 (NonVal e₁) (CPSKLet (λ m →
      cpsE𝑐 (NonVal e₂) (CPSKLet (λ n →
        CPSApp (CPSVar m) (CPSVar n) k))))

  -- P W : K
  cpsE𝑐 (NonVal (App (NonVal e₁) (Val v₂))) k =
    cpsE𝑐 (NonVal e₁) (CPSKLet (λ m →
      CPSApp (CPSVar m) (cpsV𝑐 v₂) k))

  -- V Q : K
  cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂))) k =
    cpsE𝑐 (NonVal e₂) (CPSKLet (λ n →
      CPSApp (cpsV𝑐 v₁) (CPSVar n) k))

  -- V W : K
  cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k =
    CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k

  -- Sk.M : K
  cpsE𝑐 (NonVal (Shift2 e)) k =
    CPSShift2 (λ k → cpsE𝑐 (e k) CPSKVar) k

  -- <M> : K
  cpsE𝑐 (NonVal (Reset e)) k =
    CPSRetE k (cpsE𝑐 e CPSKId)

  -- let x = M in N : K
  cpsE𝑐 (NonVal (Let e₁ e₂)) k =
    cpsE𝑐 e₁ (CPSKLet (λ m →
      cpsE𝑐 (e₂ m) k))

-- examples
test1 : {var : cpstyp → Set} → {τ₁ τ₂ : typ} →
        cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test1 = cpsV𝑐 DSterm.val1
-- CPSFun (λ x → CPSRet CPSKVar (CPSVar x))

test2 : {var : cpstyp → Set} → {τ₁ τ₂ : typ} →
        cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test2 = cpsV𝑐 DSterm.val2
-- CPSFun (λ x →
--          CPSApp CPSShift
--                 (CPSFun (λ x₁ → CPSApp (CPSVar x₁) (CPSVar x) CPSKVar))
--                 CPSKVar)

test2' : {var : cpstyp → Set} → {τ₁ τ₂ : typ} →
         cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test2' = cpsV𝑐 DSterm.val2'
-- CPSFun (λ x →
--   CPSShift2 (λ k → CPSApp (CPSVar k) (CPSVar x) CPSKVar) CPSKVar)

test3 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ τ : typ} →
        cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₂ cps[ τ₃ , τ₁ ]))
test3 {τ = τ} = cpsV𝑐 (DSterm.val3 {τ = τ})
-- λ {τ} →
--   CPSFun (λ x →
--     CPSApp CPSShift
--            (CPSFun (λ x₁ → CPSRet CPSKVar (CPSVar x)))
--            CPSKVar)

-- test4 = cpsV𝑐 DSterm.val4
-- test4' = cpsV𝑐 DSterm.val4'
{-
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

-- test5 = cpsV𝑐 DSterm.val5

-- lemma
-- e:λn.vnk -> ve:k
colon₂ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {Δ : conttyp} →
         (v₁ : value[ var ∘ cpsT ] (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ])) →
         (e₂ : term[ var ∘ cpsT , τ₄ ▷ τ₅ ] τ₃) →
         (k : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂) →
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
