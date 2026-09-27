{-
  ============================================================================
  DS 項と DSKernel 項の間の Reflection (1)  (論文 4 節, 付録 B.1)
  ============================================================================
  DS 言語の項を A-正規形変換してから DS 言語に埋め込むと、
  元の項を簡約したものになることを示す。論文の 定理 16 にあたる。
    correctV : 任意の値 V について
                 V ⟶* (V††)⊙
                 （Reduce (Val v) (Val (embedV (knormalV v)))）
    correct  : 任意の項 M と DSKernel 言語の継続 KΔ について
                 (KΔ)⊖[M] ⟶* (M :: KΔ)⊕
                 （Reduce (plug (embedC k) e) (embed (knormal e k))）
  KΔ = []Δ とすれば、M ⟶* (M :: []Δ)⊕ という本来示したかった形になる。
  帰納法を回すために、一般のコンテキスト KΔ を使った形にしている（論文 p.12）。
  証明は V, M についての相互帰納法。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect1a where

open import DSterm
open import DStermK
open import Embed

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  Generalized associativity (論文 補題 15)
  ----------------------------------------------------------------------------
  任意の DS 言語の項 e₁, e₂ と、DSKernel 言語の継続 KΔ について、
    (KΔ)⊖[let x = e₁ in e₂] ⟶* let x = e₁ in (KΔ)⊖[e₂]
  が成り立つ。つまり、let を KΔ の外に出せる。
  証明は KΔ についての場合分け。
    KΔ が []k, []• のとき     : 両辺が同じ項になる (RId)。
    KΔ が let y = [] in M のとき : (assoc) 規則 RAssoc そのもの。
  この補題は、任意の DS 言語のコンテキストでは成り立たず、
  DSKernel 言語のコンテキスト KΔ を戻した (KΔ)⊖ の形でなければならない（論文 p.18）。
-}

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

{-
  ----------------------------------------------------------------------------
  主定理 (論文 定理 16)
  ----------------------------------------------------------------------------
  各場合で、DS 言語の簡約規則 (let.1), (let.2) を使って部分式に名前を付け、
  GenAssoc で let を外に出してから、帰納法の仮定を使う。
  A-正規形変換の定義 (Embed.agda の knormal) の各場合に対応している。

  非値の場合は、Δ が K _ ▷ _ か • _ かで場合分けしているが、両者の証明は同じ。
  （Δ の形が決まらないと、計算が進まないため。）
-}

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
  -- V :: K の場合。
  correct (Val v) k = reducePlug (embedC k) (correctV v)
  -- P Q :: K の場合。
  -- (let.1) で P に、(let.2) で Q に名前を付け、GenAssoc で let を外に出す。
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
  -- P W :: K の場合。
  -- (let.1) で P に名前を付け、W は correctV で A-正規形変換する。
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
  -- V Q :: K の場合。
  -- (let.2) で Q に名前を付け、V は correctV で A-正規形変換する。
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
  -- V W :: K の場合。
  correct {Δ = K τ₁ ▷ τ₂} (NonVal (App (Val v₁) (Val v₂))) k =
    reducePlug (embedC k) (RTrans (RApp₁ (correctV v₁)) (RApp₂ (correctV v₂)))
  correct {Δ = • τ} (NonVal (App (Val v₁) (Val v₂))) k =
    reducePlug (embedC k) (RTrans (RApp₁ (correctV v₁)) (RApp₂ (correctV v₂)))
  -- Sk.M :: K の場合。本体は []k の下で帰納法の仮定を使う。
  correct {Δ = K τ₁ ▷ τ₂} (NonVal (Shift2 e)) k =
    reducePlug (embedC k) (RShift₁ (λ x → correct (e x) KVar))
  correct {Δ = • τ} (NonVal (Shift2 e)) k =
    reducePlug (embedC k) (RShift₁ (λ x → correct (e x) KVar))
  -- <M> :: K の場合。reset の中身は []• の下で帰納法の仮定を使う。
  correct {Δ = K τ₁ ▷ τ₂}(NonVal (Reset e)) k =
    reducePlug (embedC k) (RReset₁ (correct e KId))
  correct {Δ = • τ}(NonVal (Reset e)) k =
    reducePlug (embedC k) (RReset₁ (correct e KId))
  -- (let x = M in N) :: K の場合。
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
