{-# OPTIONS --rewriting #-}

module Reflect1a where

open import DSterm
open import DStermK
open import Embed

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

GenAssoc : {var : typK → Set} {τ₁ τ₂ τ₄ : typ} {α β : typK} {Δ : conttypK}
           {e₁ : term[ var ∘ knormalT , τ₂ ▷ τ₄ ] τ₁}
           {e₂ : (var ∘ knormalT) τ₂ →
                 term[ var ∘ knormalT , embedT α ▷ embedT β  ] τ₄}
           (k : pcontextK[ var , Δ , α ] β) →
           Reduce (plug (embedC k) (NonVal (Let e₁ (λ x → e₂ x))))
                  (NonVal (Let e₁ (λ x → plug (embedC k) (e₂ x))))
GenAssoc KVar = RId
GenAssoc KId = RId
GenAssoc {Δ = K τ₁ ▷ τ₂} {e₁} {e₂} (KLet e₃) =
  RAssoc e₁ e₂ (λ x → embed (e₃ x))
GenAssoc {Δ = • τ} {e₁} {e₂} (KLet e₃) = RAssoc e₁ e₂ (λ x → embed (e₃ x))

-- main theorem

mutual
  correctV : {var : typ → Set} {τ β : typ} →
             (v : value[ var ] τ) →
             Reduce {β = β} (Val v)
                             (Val (embedV {τ = knormalT τ} (knormalV  v)))
  correctV (Var x) = RId
  correctV (Num n) = RId
  correctV (Fun e) = RFun (λ x → correct (e x) KVar)
  correctV Shift = RId

  correct : {var : typK → Set} {τ₁ α β : typ} {Δ : conttypK} →
            (e : term[ var ∘ knormalT , α ▷ β ] τ₁) →
            (k : pcontextK[ var , Δ , knormalT α ] knormalT β) →
            Reduce (plug (embedC k) e) (embed {τ = knormalT τ₁} (knormal e k))
  correct (Val v) k = reducePlug (embedC k) (correctV v)
  correct {Δ = K τ₁ ▷ τ₂} (NonVal (App (NonVal e₁) (NonVal e₂))) k = begin
      plug (embedC k) (NonVal (App (NonVal e₁) (NonVal e₂)))
    ⟶⟨ reducePlug (embedC k) (RLet1 e₁ (NonVal e₂)) ⟩
      plug (embedC k)
        (NonVal
         (Let (NonVal e₁) (λ x → NonVal (App (Val (Var x)) (NonVal e₂)))))
    ⟶⟨ GenAssoc k ⟩
      NonVal
        (Let (NonVal e₁)
         (λ x → plug (embedC k) (NonVal (App (Val (Var x)) (NonVal e₂)))))
    ⟶⟨ RLet₂ (λ x → reducePlug (embedC k) (RLet2 e₂)) ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            plug (embedC k)
            (NonVal
             (Let (NonVal e₂)
              (λ y → NonVal (App (Val (Var z)) (Val (Var y))))))))
    ⟶⟨ RLet₂ (λ x → GenAssoc k) ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            NonVal
            (Let (NonVal e₂)
             (λ x →
                plug (embedC k) (NonVal (App (Val (Var z)) (Val (Var x))))))))
    ≡⟨ refl ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            plug (embedC (KLet (λ n → App (Var z) (Var n) k))) (NonVal e₂)))
    ⟶⟨ RLet₂ (λ x → correct (NonVal e₂)
                              (KLet (λ n → App (Var x) (Var n) k))) ⟩
      plug
        (embedC
         (KLet
          (λ m → knormal (NonVal e₂) (KLet (λ n → App (Var m) (Var n) k)))))
        (NonVal e₁)
    ⟶⟨ correct (NonVal e₁) (KLet
         (λ m → knormal (NonVal e₂) (KLet (λ n → App (Var m) (Var n) k)))) ⟩
      (embed
       (knormal (NonVal e₁)
        (KLet
         (λ m → knormal (NonVal e₂) (KLet (λ n → App (Var m) (Var n) k))))))
    ∎ where open DSterm.Reasoning
  correct {Δ = • τ} (NonVal (App (NonVal e₁) (NonVal e₂))) k = begin
      plug (embedC k) (NonVal (App (NonVal e₁) (NonVal e₂)))
    ⟶⟨ reducePlug (embedC k) (RLet1 e₁ (NonVal e₂)) ⟩
      plug (embedC k)
        (NonVal
         (Let (NonVal e₁) (λ x → NonVal (App (Val (Var x)) (NonVal e₂)))))
    ⟶⟨ GenAssoc k ⟩
      NonVal
        (Let (NonVal e₁)
         (λ x → plug (embedC k) (NonVal (App (Val (Var x)) (NonVal e₂)))))
    ⟶⟨ RLet₂ (λ x → reducePlug (embedC k) (RLet2 e₂)) ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            plug (embedC k)
            (NonVal
             (Let (NonVal e₂)
              (λ y → NonVal (App (Val (Var z)) (Val (Var y))))))))
    ⟶⟨ RLet₂ (λ x → GenAssoc k) ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            NonVal
            (Let (NonVal e₂)
             (λ x →
                plug (embedC k) (NonVal (App (Val (Var z)) (Val (Var x))))))))
    ≡⟨ refl ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            plug (embedC (KLet (λ n → App (Var z) (Var n) k))) (NonVal e₂)))
    ⟶⟨ RLet₂ (λ x → correct (NonVal e₂)
                              (KLet (λ n → App (Var x) (Var n) k))) ⟩
      plug
        (embedC
         (KLet
          (λ m → knormal (NonVal e₂) (KLet (λ n → App (Var m) (Var n) k)))))
        (NonVal e₁)
    ⟶⟨ correct (NonVal e₁) (KLet
         (λ m → knormal (NonVal e₂) (KLet (λ n → App (Var m) (Var n) k)))) ⟩
      (embed
       (knormal (NonVal e₁)
        (KLet
         (λ m → knormal (NonVal e₂) (KLet (λ n → App (Var m) (Var n) k))))))
    ∎ where open DSterm.Reasoning
  correct {τ₁ = τ₁} {Δ = K τ₁' ▷ τ₂'}
          (NonVal (App {τ₂ = τ₂} {τ₄ = τ₄} (NonVal e₁) (Val v))) k = begin
      plug (embedC k) (NonVal (App (NonVal e₁) (Val v)))
    ⟶⟨ reducePlug (embedC k) (RLet1 e₁ (Val v)) ⟩
      plug (embedC k)
        (NonVal
         (Let (NonVal e₁) (λ x → NonVal (App (Val (Var x)) (Val v)))))
    ⟶⟨ GenAssoc k ⟩
      NonVal
        (Let (NonVal e₁)
         (λ x → plug (embedC k) (NonVal (App (Val (Var x)) (Val v)))))
    ⟶⟨ RLet₂ (λ x → reducePlug (embedC k) (RApp₂ (correctV v))) ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            plug (embedC k)
            (NonVal (App (Val (Var z))
                         (Val (embedV {τ = knormalT τ₂} (knormalV v)))))))
    ≡⟨ refl ⟩
      plug (embedC {τ₄ = knormalT τ₄}
                   (KLet (λ m → App (Var m) (knormalV v) k)))
           (NonVal e₁)
    ⟶⟨ correct (NonVal e₁) (KLet (λ m → App (Var m) (knormalV v) k)) ⟩
      embed {τ = knormalT τ₁}
        (knormal (NonVal e₁) (KLet (λ m → App (Var m) (knormalV v) k)))
     ∎ where open DSterm.Reasoning
  correct {τ₁ = τ₁} {Δ = • τ}
          (NonVal (App {τ₂ = τ₂} {τ₄ = τ₄} (NonVal e₁) (Val v))) k = begin
      plug (embedC k) (NonVal (App (NonVal e₁) (Val v)))
    ⟶⟨ reducePlug (embedC k) (RLet1 e₁ (Val v)) ⟩
      plug (embedC k)
        (NonVal
         (Let (NonVal e₁) (λ x → NonVal (App (Val (Var x)) (Val v)))))
    ⟶⟨ GenAssoc k ⟩
      NonVal
        (Let (NonVal e₁)
         (λ x → plug (embedC k) (NonVal (App (Val (Var x)) (Val v)))))
    ⟶⟨ RLet₂ (λ x → reducePlug (embedC k) (RApp₂ (correctV v))) ⟩
      NonVal
        (Let (NonVal e₁)
         (λ z →
            plug (embedC k)
            (NonVal (App (Val (Var z))
                         (Val (embedV {τ = knormalT τ₂} (knormalV v)))))))
    ≡⟨ refl ⟩
      plug (embedC {τ₄ = knormalT τ₄}
                   (KLet (λ m → App (Var m) (knormalV v) k)))
           (NonVal e₁)
    ⟶⟨ correct (NonVal e₁) (KLet (λ m → App (Var m) (knormalV v) k)) ⟩
      embed {τ = knormalT τ₁}
        (knormal (NonVal e₁) (KLet (λ m → App (Var m) (knormalV v) k)))
     ∎ where open DSterm.Reasoning
  correct {Δ = K τ₁ ▷ τ₂} (NonVal (App (Val v₁) (NonVal e₂))) k = begin
      plug (embedC k) (NonVal (App (Val v₁) (NonVal e₂)))
    ⟶⟨ reducePlug (embedC k) (RLet2 e₂) ⟩
      plug (embedC k)
        (NonVal
         (Let (NonVal e₂) (λ x → NonVal (App (Val v₁) (Val (Var x))))))
    ⟶⟨ GenAssoc k ⟩
      NonVal
      (Let (NonVal e₂)
       (λ x →
          plug (embedC k)
          (NonVal (App (Val v₁) (Val (Var x))))))
    ⟶⟨ RLet₂ (λ x → reducePlug (embedC k) (RApp₁ (correctV v₁))) ⟩
      NonVal
      (Let (NonVal e₂)
       (λ x →
          plug (embedC k)
          (NonVal (App (Val (embedV {τ = knormalT _} (knormalV v₁)))
                       (Val (Var x))))))
    ≡⟨ refl ⟩
      plug (embedC (KLet (λ n → App (knormalV v₁) (Var n) k))) (NonVal e₂)
    ⟶⟨ correct (NonVal e₂) (KLet (λ n → App (knormalV v₁) (Var n) k)) ⟩
      embed (knormal (NonVal e₂) (KLet (λ n → App (knormalV v₁) (Var n) k)))
    ∎ where open DSterm.Reasoning
  correct {Δ = • τ} (NonVal (App (Val v₁) (NonVal e₂))) k = begin
      plug (embedC k) (NonVal (App (Val v₁) (NonVal e₂)))
    ⟶⟨ reducePlug (embedC k) (RLet2 e₂) ⟩
      plug (embedC k)
        (NonVal
         (Let (NonVal e₂) (λ x → NonVal (App (Val v₁) (Val (Var x))))))
    ⟶⟨ GenAssoc k ⟩
      NonVal
      (Let (NonVal e₂)
       (λ x →
          plug (embedC k)
          (NonVal (App (Val v₁) (Val (Var x))))))
    ⟶⟨ RLet₂ (λ x → reducePlug (embedC k) (RApp₁ (correctV v₁))) ⟩
      NonVal
      (Let (NonVal e₂)
       (λ x →
          plug (embedC k)
          (NonVal (App (Val (embedV {τ = knormalT _} (knormalV v₁)))
                       (Val (Var x))))))
    ≡⟨ refl ⟩
      plug (embedC (KLet (λ n → App (knormalV v₁) (Var n) k))) (NonVal e₂)
    ⟶⟨ correct (NonVal e₂) (KLet (λ n → App (knormalV v₁) (Var n) k)) ⟩
      embed (knormal (NonVal e₂) (KLet (λ n → App (knormalV v₁) (Var n) k)))
    ∎ where open DSterm.Reasoning
  correct {Δ = K τ₁ ▷ τ₂} (NonVal (App (Val v₁) (Val v₂))) k =
    reducePlug (embedC k) (RTrans (RApp₁ (correctV v₁)) (RApp₂ (correctV v₂)))
  correct {Δ = • τ} (NonVal (App (Val v₁) (Val v₂))) k =
    reducePlug (embedC k) (RTrans (RApp₁ (correctV v₁)) (RApp₂ (correctV v₂)))
  correct {Δ = K τ₁ ▷ τ₂} (NonVal (Shift2 e)) k =
    reducePlug (embedC k) (RShift₁ (λ x → correct (e x) KVar))
  correct {Δ = • τ} (NonVal (Shift2 e)) k =
    reducePlug (embedC k) (RShift₁ (λ x → correct (e x) KVar))
  correct {Δ = K τ₁ ▷ τ₂}(NonVal (Reset e)) k =
    reducePlug (embedC k) (RReset₁ (correct e KId))
  correct {Δ = • τ}(NonVal (Reset e)) k =
    reducePlug (embedC k) (RReset₁ (correct e KId))
  correct {var} {Δ = K τ₁ ▷ τ₂} (NonVal (Let e₁ e₂)) k = begin
      plug (embedC k) (NonVal (Let e₁ e₂))
    ⟶⟨ GenAssoc k ⟩
      NonVal (Let e₁ (λ x → plug (embedC k) (e₂ x)))
    ⟶⟨ RLet₂ (λ x → correct (e₂ x) k) ⟩
      NonVal (Let e₁ (λ x → embed {τ = knormalT _} (knormal (e₂ x) k)))
    ≡⟨ refl ⟩
      plug (embedC (KLet (λ m → knormal (e₂ m) k))) e₁
    ⟶⟨ correct e₁ (KLet (λ m → knormal (e₂ m) k)) ⟩
      embed (knormal e₁ (KLet (λ m → knormal (e₂ m) k)))
    ∎ where open DSterm.Reasoning
  correct {var} {Δ = • τ} (NonVal (Let e₁ e₂)) k = begin
      plug (embedC k) (NonVal (Let e₁ e₂))
    ⟶⟨ GenAssoc k ⟩
      NonVal (Let e₁ (λ x → plug (embedC k) (e₂ x)))
    ⟶⟨ RLet₂ (λ x → correct (e₂ x) k) ⟩
      NonVal (Let e₁ (λ x → embed {τ = knormalT _} (knormal (e₂ x) k)))
    ≡⟨ refl ⟩
      plug (embedC (KLet (λ m → knormal (e₂ m) k))) e₁
    ⟶⟨ correct e₁ (KLet (λ m → knormal (e₂ m) k)) ⟩
      embed (knormal e₁ (KLet (λ m → knormal (e₂ m) k)))
    ∎ where open DSterm.Reasoning
