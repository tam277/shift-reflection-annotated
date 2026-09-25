{-# OPTIONS --rewriting #-}

module DecomposeColon where

open import CPSterm
open import DSterm
open import DStermK
open import DSTrans
open import Embed
open import CPSColonTrans
open import Reflect2a hiding (correctV; correct)
open import Reflect2b hiding (correctV; correct)

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Extensionality

-- for REWRITE
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

cpsE∘knormalT : (τ : typ) → CPSColonTrans.cpsT τ ≡ DSTrans.cpsT (knormalT τ)
cpsE∘knormalT Nat = refl
cpsE∘knormalT (τ ⇒ τ₁ cps[ τ₂ , τ₃ ])
  rewrite cpsE∘knormalT τ
        | cpsE∘knormalT τ₁
        | cpsE∘knormalT τ₂
        | cpsE∘knormalT τ₃ = refl

{-# REWRITE cpsE∘knormalT #-}

--main theorem

mutual
  correctV : {var : cpstyp → Set} →
             {τ₁ : typ} →
             (v : value[ var ∘ CPSColonTrans.cpsT ] τ₁) →
             cpsV𝑐 {var} v ≡ cpsV {τ₁ = knormalT τ₁} (knormalV v)

  correctV (Var v) = refl
  correctV (Num n) = refl
  correctV (Fun e) = cong CPSFun (extensionality (λ x → correct (e x) KVar))
  correctV Shift = refl

  correct : {var : cpstyp → Set} →
            {τ₁ τ₂ τ : typ}  → {Δ : conttypK}
            (e : term[ var ∘ CPSColonTrans.cpsT , τ₁ ▷ τ₂ ] τ) →
            (k : pcontextK[ var ∘ DSTrans.cpsT , Δ , knormalT τ₁ ]
                 knormalT τ₂) →
            cpsE𝑐 {var} e (cpsC {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂} k) ≡
            cpsE {τ = knormalT τ} (knormal e k)

  correct (Val v) k = cong (CPSRet (cpsC k)) (correctV v)
  correct (NonVal (App (Val v₁) (Val v₂))) k =
    cong₂ (λ x y → CPSApp x y (cpsC k)) (correctV v₁) (correctV v₂)
  correct {var} (NonVal (App (Val v₁) (NonVal e₂))) k
    with correct {var} (NonVal e₂)
  ... | eq₂ rewrite correctV {var} v₁ =
    eq₂ (KLet (λ n → App (knormalV v₁) (Var n) k))
  correct {var} {τ₁} {τ₂} {τ = τ}
          (NonVal (App {τ₂ = τ₂'} {τ₄ = τ₄} (NonVal e₁) (Val v₂))) k
    with correct {var} (NonVal e₁)
  ... | eq₁ rewrite correctV {var} v₂ =
    eq₁ (KLet (λ m → App {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂'}
                          {τ₃ = knormalT τ₂} (Var m) (knormalV v₂) k))
  correct {var} {τ₁} {τ₂} {τ} {K _ ▷ _}
          (NonVal (App {τ₂ = τ₂'} {τ₄ = τ₄} {τ₅} (NonVal e₁) (NonVal e₂))) k
    with correct {var} (NonVal e₁) | correct {var} (NonVal e₂)
  ... | eq₁ | eq₂ = begin
      cpsE𝑐 (NonVal e₁)
      (CPSKLet
       (λ m →
          cpsE𝑐 (NonVal e₂)
          (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) (cpsC k)))))
    ≡⟨ cong (cpsE𝑐 (NonVal e₁)) (cong CPSKLet (extensionality (λ x →
         eq₂ (KLet (λ n → App {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂'}
                               {τ₃ = knormalT τ₂} (Var x) (Var n) k))))) ⟩
      cpsE𝑐 (NonVal e₁)
        (cpsC {τ₁ = knormalT (τ₂' ⇒ τ₁ cps[ τ₂ , τ₄ ])} {τ₂ = knormalT τ₅}
          (KLet (λ m →
            knormal (NonVal e₂)
                    (KLet (λ n → App {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂'}
                                     {τ₃ = knormalT τ₂} (Var m) (Var n) k)))))
    ≡⟨ eq₁ _ ⟩
      cpsE (knormal (NonVal e₁) (KLet (λ m →
        knormal (NonVal e₂) (KLet (λ n → App {τ₂ = knormalT τ₂'}
                                              (Var m) (Var n) k)))))
    ∎ where open ≡-Reasoning
  correct {var} {τ₁} {τ₂} {τ} {• _}
          (NonVal (App {τ₂ = τ₂'} {τ₄ = τ₄} {τ₅} (NonVal e₁) (NonVal e₂))) k
    with correct {var} (NonVal e₁) | correct {var} (NonVal e₂)
  ... | eq₁ | eq₂ = begin
      cpsE𝑐 (NonVal e₁)
      (CPSKLet
       (λ m →
          cpsE𝑐 (NonVal e₂)
          (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) (cpsC k)))))
    ≡⟨ cong (cpsE𝑐 (NonVal e₁)) (cong CPSKLet (extensionality (λ x →
         eq₂ (KLet (λ n → App {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂'}
                               {τ₃ = knormalT τ₂} (Var x) (Var n) k))))) ⟩
      cpsE𝑐 (NonVal e₁)
        (cpsC {τ₁ = knormalT (τ₂' ⇒ τ₁ cps[ τ₂ , τ₄ ])} {τ₂ = knormalT τ₅}
          (KLet (λ m →
            knormal (NonVal e₂)
                    (KLet (λ n → App {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂'}
                                     {τ₃ = knormalT τ₂} (Var m) (Var n) k)))))
    ≡⟨ eq₁ _ ⟩
      cpsE (knormal (NonVal e₁) (KLet (λ m →
        knormal (NonVal e₂) (KLet (λ n → App {τ₂ = knormalT τ₂'}
                                              (Var m) (Var n) k)))))
    ∎ where open ≡-Reasoning
  correct (NonVal (Shift2 e)) k =
    cong₂ CPSShift2 (extensionality (λ k → correct (e k) KVar)) refl
  correct (NonVal (Reset e)) k =
    cong (CPSRetE (cpsC k)) (correct e KId)
  correct (NonVal (Let (Val v₁) e₂)) k =
    cong₂ CPSRet (cong CPSKLet (extensionality (λ x →
      correct (e₂ x) k))) (correctV v₁)
  correct {var} {τ₁} {τ₂} {Δ = K _ ▷ _}
          (NonVal (Let {τ₁'} {β} (NonVal e₁) e₂)) k
    with correct {var} (NonVal e₁)
  ... | eq₁ = begin
      cpsE𝑐 (NonVal e₁) (CPSKLet (λ m →
        cpsE𝑐 (e₂ m) (cpsC {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂} k)))
    ≡⟨ cong (cpsE𝑐 (NonVal e₁)) (cong CPSKLet (extensionality (λ x →
         correct (e₂ x) k))) ⟩
      cpsE𝑐 (NonVal e₁) (cpsC {τ₁ = knormalT τ₁'} {τ₂ = knormalT β}
                              (KLet (λ m → knormal (e₂ m) k)))
    ≡⟨ eq₁ _ ⟩
      cpsE (knormal (NonVal e₁) (KLet (λ m → knormal (e₂ m) k)))
    ∎ where open ≡-Reasoning
  correct {var} {τ₁} {τ₂} {Δ = • _}
          (NonVal (Let {τ₁'} {β} (NonVal e₁) e₂)) k
    with correct {var} (NonVal e₁)
  ... | eq₁ = begin
      cpsE𝑐 (NonVal e₁) (CPSKLet (λ m →
        cpsE𝑐 (e₂ m) (cpsC {τ₁ = knormalT τ₁} {τ₂ = knormalT τ₂} k)))
    ≡⟨ cong (cpsE𝑐 (NonVal e₁)) (cong CPSKLet (extensionality (λ x →
         correct (e₂ x) k))) ⟩
      cpsE𝑐 (NonVal e₁) (cpsC {τ₁ = knormalT τ₁'} {τ₂ = knormalT β}
                              (KLet (λ m → knormal (e₂ m) k)))
    ≡⟨ eq₁ _ ⟩
      cpsE (knormal (NonVal e₁) (KLet (λ m → knormal (e₂ m) k)))
    ∎ where open ≡-Reasoning

maincorrectC : {var : cpstyp → Set} {τ τ₁ τ₂ α β : cpstyp} →
               (k : cpscont[ var , K α ⇒ β , τ₁ ] τ₂) →
               (e : term[ var ∘ DSTrans.cpsT ∘ knormalT ,
                          embedT (dsT τ₁) ▷ embedT (dsT τ₂) ]
                        embedT (dsT τ)) →
               cpsE (knormal (plug (embedC (dsC k)) e) KVar) ≡ cpsE𝑐 e k
maincorrectC {var} {τ} k e
  rewrite Reflect2b.correctC {var ∘ DSTrans.cpsT} {dsT τ} (dsC k) e
        | sym (correct e (dsC k))
        | Reflect2a.correctC {var ∘ DSTrans.cpsT} k = refl

maincorrectC2 : {var : cpstyp → Set} {τ τ₁ τ₂ γ : cpstyp} →
                (k : cpscont[ var , • γ , τ₁ ] τ₁) →
                (e : term[ var ∘ DSTrans.cpsT ∘ knormalT ,
                           embedT (dsT τ₁) ▷ embedT (dsT τ₁) ]
                         embedT (dsT τ)) →
                cpsE (knormal (plug (embedC (dsC k)) e) KId) ≡ cpsE𝑐 e k
maincorrectC2 {var} {τ} k e
  rewrite Reflect2b.correctC2 {var ∘ DSTrans.cpsT} {dsT τ} (dsC k) e
        | sym (correct e (dsC k))
        | Reflect2a.correctC {var ∘ DSTrans.cpsT} k = refl
