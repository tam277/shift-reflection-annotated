module DStermK where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- type
data typK : Set where
  Nat          : typK
  _⇒_cps[_,_]  : typK → typK → typK → typK → typK

data conttypK : Set where
  K_▷_ : typK → typK → conttypK
  •_ : typK → conttypK

Δ-typeK : conttypK → typK → typK → Set
Δ-typeK (K τ₁′ ▷ τ₂′) τ₁ τ₂ = τ₁′ ≡ τ₁ × τ₂′ ≡ τ₂
Δ-typeK (• τ) τ₁ τ₂ = τ ≡ τ₁ × τ ≡ τ₂

-- source kernel term
mutual
  data valueK[_]_ (var : typK → Set) : typK → Set where
    -- x
    Var   : {τ₁ : typK} → var τ₁ → valueK[ var ] τ₁
    -- n
    Num   : ℕ → valueK[ var ] Nat
    -- λx.M
    Fun   : {τ₀ τ₁ τ₃ τ₄ : typK} →
            (var τ₀ → termK[ var , K τ₁ ▷ τ₃ ] τ₄) →
            valueK[ var ] (τ₀ ⇒ τ₁ cps[ τ₃ , τ₄ ])
    -- S
    Shift : {τ₁ τ₂ τ₃ τ₄ τ₅ : typK} →
            valueK[ var ]
            (((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])
             ⇒ τ₁ cps[ τ₂ , τ₅ ])

  data termK[_,_]_ (var : typK → Set) : conttypK → typK → Set where
    -- K V
    Ret  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
           pcontextK[ var , Δ , τ₁ ] τ₂ →
           valueK[ var ] τ₁ →
           termK[ var , Δ ] τ₂
    -- K (V W)
    App  : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
           valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) →
           valueK[ var ] τ₂ →
           pcontextK[ var , Δ , τ₁ ] τ₃ →
           termK[ var , Δ ] τ₄
    -- K (Sk.M)
    Shift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ : typK} → {Δ : conttypK} →
           (var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → termK[ var , K τ₄ ▷ τ₄ ] τ₅) →
           pcontextK[ var , Δ , τ₁ ] τ₂ →
           termK[ var , Δ ] τ₅
    -- K <M>
    RetE : {τ τ₁ τ₂ : typK} → {Δ : conttypK} →
           pcontextK[ var , Δ , τ₁ ] τ₂ →
           termK[ var , • τ ] τ₁ →
           termK[ var , Δ ] τ₂

  data pcontextK[_,_,_]_ (var : typK → Set) : conttypK → typK → typK → Set where
    -- k []
    KVar  : {τ₁ τ₂ : typK} →
            pcontextK[ var , K τ₁ ▷ τ₂ , τ₁ ] τ₂
    -- []
    KId   : {τ₁ : typK} →
            pcontextK[ var , • τ₁ , τ₁ ] τ₁
    -- let x = [] in M
    KLet  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
            (e₂ : var τ₁ → termK[ var , Δ ] τ₂) →
            pcontextK[ var , Δ , τ₁ ] τ₂

-- example
-- λx.λk.k@x
val1 : {var : typK → Set} → {τ₁ τ₂ : typK} →
       valueK[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val1 = Fun (λ x → Ret KVar (Var x))

-- interpreter
〚_〛 : typK → Set
〚 Nat 〛 = ℕ
〚 τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] 〛 =
   〚 τ₂ 〛 → (〚 τ₁ 〛 → 〚 τ₃ 〛) → 〚 τ₄ 〛

〚_〛' : conttypK → Set
〚 K τ₂ ▷ τ₁ 〛' = 〚 τ₂ 〛 → 〚 τ₁ 〛
〚 • τ 〛' = 〚 τ 〛 → 〚 τ 〛

mutual
  gv : {τ : typK} → valueK[ 〚_〛 ] τ → 〚 τ 〛
  gv (Var x) = x
  gv (Num n) = n
  gv (Fun e) = λ x k → g (e x) k
  gv Shift = λ v k → v (λ x₂ k₂ → k₂ (k x₂)) (λ x → x)

  g : {τ : typK} → {Δ : conttypK} → termK[ 〚_〛 , Δ ] τ → 〚 Δ 〛' → 〚 τ 〛
  g (Ret k v) Δ = (gc k Δ) (gv v)
  g (App v w k) Δ = (gv v) (gv w) (gc k Δ)
  g (Shift2 e k) Δ = g (e (λ x₂ k₂ → k₂ (gc k Δ x₂))) (λ x → x)
  g (RetE k e) Δ = (gc k Δ) (g e (λ x → x))

  gc : {τ₁ τ₂ : typK} {Δ : conttypK} →
       pcontextK[ 〚_〛 , Δ , τ₁ ] τ₂ → 〚 Δ 〛'  → 〚 τ₁ 〛 → 〚 τ₂ 〛
  gc KVar k = k
  gc KId Δ = λ x → x
  gc (KLet e) Δ = λ x → g (e x) Δ

mutual
  data SubstVK {var : typK → Set} : {τ τ₁ : typK} →
               (var τ → valueK[ var ] τ₁) →
               valueK[ var ] τ →
               valueK[ var ] τ₁ → Set where
    sVar=  : {τ : typK} {v : valueK[ var ] τ} →
             SubstVK (λ x → Var x) v v
    sVar≠  : {τ τ₁ : typK} {v : valueK[ var ] τ} {x : var τ₁} →
             SubstVK (λ _ → Var x) v (Var x)
    sNum   : {τ : typK} {v : valueK[ var ] τ} {n : ℕ} →
             SubstVK (λ _ → Num n) v (Num n)
    sFun   : {τ′ τ₀ τ₁ τ₃ τ₄ : typK} →
             {e  : var τ′ → var τ₀ → termK[ var , K τ₁ ▷ τ₃ ] τ₄} →
             {v  : valueK[ var ] τ′} →
             {e′ : var τ₀ → termK[ var , K τ₁ ▷ τ₃ ] τ₄} →
             ((x : var τ₀) → SubstK (λ y → (e y) x) v (e′ x)) →
             SubstVK (λ y → Fun (λ x → (e y) x)) v (Fun e′)
    sShift : {τ₁ τ₂ τ₃ τ₄ τ₅ τ : typK} {v : valueK[ var ] τ} →
             SubstVK (λ _ → Shift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅})
                     v Shift

  data SubstK {var : typK → Set} : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              (var τ₁ → termK[ var , Δ ] τ₂) →
              valueK[ var ] τ₁ →
              termK[ var , Δ ] τ₂ → Set where
    sRet   : {τ τ₁ τ₂ : typK} → {Δ : conttypK} →
             {k₁ : var τ → pcontextK[ var , Δ , τ₁ ] τ₂} →
             {v₁ : var τ → valueK[ var ] τ₁} →
             {v : valueK[ var ] τ} →
             {k₂ : pcontextK[ var , Δ , τ₁ ] τ₂} →
             {v₂ : valueK[ var ] τ₁} →
             SubstCK k₁ v k₂ →
             SubstVK v₁ v v₂ →
             SubstK (λ y → Ret (k₁ y) (v₁ y)) v (Ret k₂ v₂)
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
             {v₁ : var τ → valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
             {w₁ : var τ → valueK[ var ] τ₂} →
             {k₁ : var τ → pcontextK[ var , Δ , τ₁ ] τ₃} →
             {v  : valueK[ var ] τ} →
             {v₂ : valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
             {w₂ : valueK[ var ] τ₂} →
             {k₂ : pcontextK[ var , Δ , τ₁ ] τ₃} →
             SubstVK v₁ v v₂ →
             SubstVK w₁ v w₂ →
             SubstCK k₁ v k₂ →
             SubstK (λ y → (App (v₁ y) (w₁ y) (k₁ y))) v (App v₂ w₂ k₂)
    sShift2 : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typK} → {Δ : conttypK} →
             {e₁ : var τ → var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                   termK[ var , K τ₄ ▷ τ₄ ] τ₅} →
             {k₁ : var τ → pcontextK[ var , Δ , τ₁ ] τ₂} →
             {v  : valueK[ var ] τ} →
             {e₂ : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                   termK[ var , K τ₄ ▷ τ₄ ] τ₅} →
             {k₂ : pcontextK[ var , Δ , τ₁ ] τ₂} →
             ((x : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ])) →
              SubstK (λ y → (e₁ y) x) v (e₂ x)) →
             SubstCK k₁ v k₂ →
             SubstK (λ y → (Shift2 (e₁ y) (k₁ y))) v (Shift2 e₂ k₂)
    sRetE  : {τ τ₁ τ₂ α : typK} → {Δ : conttypK} →
             {k₁ : var τ → pcontextK[ var , Δ , τ₁ ] τ₂} →
             {e₁ : var τ → termK[ var , • α ] τ₁} →
             {v  : valueK[ var ] τ} →
             {k₂ : pcontextK[ var , Δ , τ₁ ] τ₂} →
             {e₂ : termK[ var , • α ] τ₁} →
             SubstCK k₁ v k₂ → SubstK e₁ v e₂ →
             SubstK (λ y → (RetE (k₁ y) (e₁ y))) v (RetE k₂ e₂)

  data SubstCK {var : typK → Set} : {τ α β : typK} → {Δ : conttypK} →
               (var τ → pcontextK[ var , Δ , α ] β) →
               valueK[ var ] τ →
               pcontextK[ var , Δ , α ] β → Set where
    sKVar≠   : {τ τ₁ τ₂ : typK} →
               {v : valueK[ var ] τ} →
               SubstCK (λ _ → KVar {τ₁ = τ₁} {τ₂}) v KVar
    sKId     : {τ τ₁ : typK} →
               {v : valueK[ var ] τ} →
               SubstCK (λ _ → KId {τ₁ = τ₁}) v KId
    sKLet    : {τ τ₁ τ₂ : typK} → {Δ : conttypK} →
               {e₁ : var τ → var τ₁ → termK[ var , Δ ] τ₂} →
               {v  : valueK[ var ] τ} →
               {e₂ : var τ₁ → termK[ var , Δ ] τ₂} →
               ((x : var τ₁) → SubstK (λ y → (e₁ y) x) v (e₂ x)) →
               SubstCK (λ y → KLet (e₁ y)) v (KLet e₂)

mutual
  data SubstK₂ {var : typK → Set} :
               {τ₁ α β : typK} → {Δ : conttypK} →
               termK[ var , K α ▷ β ] τ₁ → -- has to be K
               pcontextK[ var , Δ , α ] β →
               termK[ var , Δ ] τ₁ → Set where
    sRet    : {τ₁ τ₂ α β : typK} → {Δ : conttypK}
              {k₁ : pcontextK[ var , K α ▷ β , τ₁ ] τ₂} →
              {v  : valueK[ var ] τ₁} →
              {c  : pcontextK[ var , Δ , α ] β} →
              {k₂ : pcontextK[ var , Δ , τ₁ ] τ₂} →
              SubstCK₂ k₁ c k₂ →
              SubstK₂ (Ret k₁ v) c (Ret k₂ v)
    sApp    : {τ₁ τ₂ τ₃ τ₄ α β : typK} → {Δ : conttypK} →
              {v  : valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
              {w  : valueK[ var ] τ₂} →
              {k₁ : pcontextK[ var , K α ▷ β , τ₁ ] τ₃} →
              {c  : pcontextK[ var , Δ , α ] β} →
              {k₂ : pcontextK[ var , Δ , τ₁ ] τ₃} →
              SubstCK₂ k₁ c k₂ →
              SubstK₂ (App v w k₁) c (App v w k₂)
    sShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ α β : typK} → {Δ : conttypK} →
              {e  : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                    termK[ var , K τ₄ ▷ τ₄ ] τ₅} →
              {k₁ : pcontextK[ var , K α ▷ β , τ₁ ] τ₂} →
              {c  : pcontextK[ var , Δ , α ] β} →
              {k₂ : pcontextK[ var , Δ , τ₁ ] τ₂} →
              SubstCK₂ k₁ c k₂ →
              SubstK₂ (Shift2 e k₁) c (Shift2 e k₂)
    sRetE   : {τ₁ τ₂ α β γ : typK} → {Δ : conttypK} →
              {k₁ : pcontextK[ var , K α ▷ β , τ₁ ] τ₂} →
              {e  : termK[ var , • γ ] τ₁} →
              {c  : pcontextK[ var , Δ , α ] β} →
              {k₂ : pcontextK[ var , Δ , τ₁ ] τ₂} →
              SubstCK₂ k₁ c k₂ →
              SubstK₂ (RetE k₁ e) c (RetE k₂ e)

  data SubstCK₂ {var : typK → Set} :
                {τ₁ τ₂ α β : typK} → {Δ : conttypK} →
                pcontextK[ var , K α ▷ β , τ₁ ] τ₂ →
                pcontextK[ var , Δ , α ] β →
                pcontextK[ var , Δ , τ₁ ] τ₂ → Set where
    sKVar=  : {α β : typK} → {Δ : conttypK} →
              {c : pcontextK[ var , Δ , α ] β} →
              SubstCK₂ KVar c c
    sKLet   : {τ₁ τ₂ α β : typK} → {Δ : conttypK} →
              {e₁ : var τ₁ → termK[ var , K α ▷ β ] τ₂} →
              {c  : pcontextK[ var , Δ , α ] β} →
              {e₂ : var τ₁ → termK[ var , Δ ] τ₂} →
              ((x : var τ₁) → SubstK₂ (e₁ x) c (e₂ x)) →
              SubstCK₂ (KLet e₁) c (KLet e₂)

-- reduction rules
mutual
  data ReduceK {var : typK → Set} : {τ₁ : typK} → {Δ : conttypK} →
               termK[ var , Δ ] τ₁ →
               termK[ var , Δ ] τ₁ → Set where
    -- K ((λx.M) V) -> M[x:=V][k:=K]
    RBetaV  : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
              {e₁ : var τ₂ → termK[ var , K τ₁ ▷ τ₃ ] τ₄} →
              {v : valueK[ var ] τ₂} →
              {c : pcontextK[ var , Δ , τ₁ ] τ₃} →
              {e₁′ : termK[ var , K τ₁ ▷ τ₃ ] τ₄} →
              {e₂ : termK[ var , Δ ] τ₄} →
              SubstK e₁ v e₁′ →
              SubstK₂ e₁′ c e₂ →
              ReduceK (App (Fun (λ x → e₁ x)) v c) e₂
    -- let x = V in M -> M[x:=V]
    RBetaLet : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {e  : var τ₁ → termK[ var , Δ ] τ₂} →
              {v  : valueK[ var ] τ₁} →
              {e′ : termK[ var , Δ ] τ₂} →
              SubstK e v e′ →
              ReduceK (Ret (KLet e) v) e′
    -- K <J[S@V]> -> K <V@(λy.<J[y]>)>
    RShift  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typK} → {Δ : conttypK} →
              {v  : valueK[ var ]
                    ((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])} →
              {j  : pcontextK[ var , • τ₄ , τ₁ ] τ₂} →
              {k : pcontextK[ var , Δ , τ₅ ] τ₆} →
              ReduceK (RetE k (App Shift v j))
                      (RetE k (App v (Fun (λ y → RetE KVar (Ret j (Var y))))
                                   KId))
    -- K <J[Sk.M]> -> K <(λk.M)@(λy.<J[y]>)>
    RShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typK} → {Δ : conttypK} →
              {e  : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                    termK[ var ,  K τ₄ ▷ τ₄ ] τ₅} →
              {j  : pcontextK[ var , • τ₄ , τ₁ ] τ₂} →
              {k : pcontextK[ var , Δ , τ₅ ] τ₆} →
              ReduceK (RetE k (Shift2 e j))
                      (RetE k (App (Fun e)
                                   (Fun (λ y → RetE KVar (Ret j (Var y))))
                                   KId))
    -- k <V> -> k V
    RReset  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {v : valueK[ var ] τ₁} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₂} →
              ReduceK (RetE k (Ret KId v)) (Ret k v)

    -- congruence rules
    RRet₁   : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {k k' : pcontextK[ var , Δ , τ₁ ] τ₂} →
              {v : valueK[ var ] τ₁} →
              ReduceCK k k' →
              ReduceK (Ret k v) (Ret k' v)
    RRet₂   : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₂} →
              {v v' : valueK[ var ] τ₁} →
              ReduceVK v v' →
              ReduceK (Ret k v) (Ret k v')
    RApp₁   : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
              {v v' : valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
              {w : valueK[ var ] τ₂} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₃} →
              ReduceVK v v' →
              ReduceK (App v w k) (App v' w k)
    RApp₂   : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
              {v : valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
              {w w' : valueK[ var ] τ₂} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₃} →
              ReduceVK w w' →
              ReduceK (App v w k) (App v w' k)
    RApp₃   : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
              {v : valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
              {w : valueK[ var ] τ₂} →
              {k k' : pcontextK[ var , Δ , τ₁ ] τ₃} →
              ReduceCK k k' →
              ReduceK (App v w k) (App v w k')
    RShift₁  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typK} → {Δ : conttypK} →
              {k k' : pcontextK[ var , Δ , τ₁ ] τ₂} →
              {e : (var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                   termK[ var , K τ₄ ▷ τ₄ ] τ₅)} →
              ReduceCK k k' →
              ReduceK (Shift2 e k) (Shift2 e k')
    RShift₂  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typK} → {Δ : conttypK} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₂} →
              {e e' : (var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                   termK[ var , K τ₄ ▷ τ₄ ] τ₅)} →
              ((x : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ])) → ReduceK (e x) (e' x)) →
              ReduceK (Shift2 e k) (Shift2 e' k)
    RRetE₁  : {τ τ₁ τ₂ : typK} → {Δ : conttypK} →
              {k k' : pcontextK[ var , Δ , τ₁ ] τ₂} →
              {e : termK[ var , • τ ] τ₁} →
              ReduceCK k k' →
              ReduceK (RetE k e) (RetE k' e)
    RRetE₂  : {τ τ₁ τ₂ : typK} → {Δ : conttypK} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₂} →
              {e e' : termK[ var , • τ ] τ₁} →
              ReduceK e e' →
              ReduceK (RetE k e) (RetE k e')
    -- closure rules
    RId     : {τ₁ : typK} {Δ : conttypK} →
              {e : termK[ var , Δ ] τ₁} →
              ReduceK e e
    RTrans  : {τ₁ : typK} {Δ : conttypK} →
              {e₁ e₂ e₃ : termK[ var , Δ ] τ₁} →
              ReduceK e₁ e₂ →
              ReduceK e₂ e₃ →
              ReduceK e₁ e₃

  data ReduceVK {var : typK → Set} : {τ₁ : typK} →
                valueK[ var ] τ₁ →
                valueK[ var ] τ₁ → Set where
    -- λx.V x -> V
    REtaV   : {τ₁ τ₂ τ₃ τ₄ : typK} →
              (v : valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])) →
              ReduceVK (Fun (λ x → App v (Var x) KVar)) v

    -- congruence rule
    RFun    : {τ₀ τ₁ τ₃ τ₄ : typK} →
              (e e' : var τ₀ → termK[ var , K τ₁ ▷ τ₃ ] τ₄) →
              ((x : var τ₀) → ReduceK (e x) (e' x)) →
              ReduceVK (Fun e) (Fun e')
    -- closure rules
    RId     : {τ₁ : typK} →
              {v : valueK[ var ] τ₁} →
              ReduceVK v v
    RTrans  : {τ₁ : typK} →
              {v₁ v₂ v₃ : valueK[ var ] τ₁} →
              ReduceVK v₁ v₂ →
              ReduceVK v₂ v₃ →
              ReduceVK v₁ v₃

  data ReduceCK {var : typK → Set} : {τ₁ τ₂ : typK} → {Δ : conttypK} →
                pcontextK[ var , Δ , τ₁ ] τ₂ →
                pcontextK[ var , Δ , τ₁ ] τ₂ → Set where
    -- let x = [] in K x -> K
    REtaLet : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              (k : pcontextK[ var , Δ , τ₁ ] τ₂) →
              ReduceCK (KLet (λ x → Ret k (Var x))) k

    -- congruence rule
    RKLet   : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {e e' : var τ₁ → termK[ var , Δ ] τ₂} →
              ((x : var τ₁) → ReduceK (e x) (e' x)) →
              ReduceCK (KLet e) (KLet e')
    -- closure rules
    RId     : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₂} →
              ReduceCK k k
    RTrans  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {k₁ k₂ k₃ : pcontextK[ var , Δ , τ₁ ] τ₂} →
              ReduceCK k₁ k₂ →
              ReduceCK k₂ k₃ →
              ReduceCK k₁ k₃

-- equational reasoning
module Reasoning where

  open import Relation.Binary.PropositionalEquality

  infix  3 _∎
  infixr 2 _⟶⟨_⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : {var : typK → Set} {τ₁ : typK} {Δ : conttypK} →
           {e₁ e₂ : termK[ var , Δ ] τ₁} →
           ReduceK e₁ e₂ → ReduceK e₁ e₂
  begin_ red = red

  _⟶⟨_⟩_ : {var : typK → Set} {τ₁ : typK} {Δ : conttypK} →
            (e₁ {e₂ e₃} : termK[ var , Δ ] τ₁) →
            ReduceK e₁ e₂ → ReduceK e₂ e₃ → ReduceK e₁ e₃
  _⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red-e₃ = RTrans e₁-red-e₂ e₂-red-e₃

  _≡⟨_⟩_ : {var : typK → Set} {τ₁ : typK} {Δ : conttypK} →
           (e₁ {e₂ e₃} : termK[ var , Δ ] τ₁) →
           e₁ ≡ e₂ → ReduceK e₂ e₃ →
           ReduceK e₁ e₃
  _≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red-e₃ = e₂-red-e₃

  _∎ : {var : typK → Set} {τ₁ : typK} {Δ : conttypK} →
       (e : termK[ var , Δ ] τ₁) → ReduceK e e
  _∎ e = RId

-- lemma
mutual
  SubstKV≠ : {var : typK → Set} {τ₁ τ : typK} →
             (v₁ : valueK[ var ] τ₁) →
             {v : valueK[ var ] τ} →
             SubstVK (λ _ → v₁) v v₁
  SubstKV≠ (Var x) = sVar≠
  SubstKV≠ (Num n) = sNum
  SubstKV≠ (Fun e) = sFun (λ x → SubstK≠ (e x))
  SubstKV≠ Shift = sShift

  SubstK≠ : {var : typK → Set} {τ₄ τ : typK} {Δ : conttypK} →
            (e₁ : termK[ var , Δ ] τ₄) →
            {v : valueK[ var ] τ} →
            SubstK (λ _ → e₁) v e₁
  SubstK≠ (Ret k v) = sRet (SubstKC≠ k) (SubstKV≠ v)
  SubstK≠ (App v w k) = sApp (SubstKV≠ v) (SubstKV≠ w) (SubstKC≠ k)
  SubstK≠ (Shift2 e k) = sShift2 (λ x → SubstK≠ (e x)) (SubstKC≠ k)
  SubstK≠ (RetE k e) = sRetE (SubstKC≠ k) (SubstK≠ e)

  SubstKC≠ : {var : typK → Set} {τ₂ τ₄ τ : typK} {Δ : conttypK} →
             (k₁ : pcontextK[ var , Δ , τ₂ ] τ₄) →
             {v : valueK[ var ] τ} →
             SubstCK (λ _ → k₁) v k₁
  SubstKC≠ KVar = sKVar≠
  SubstKC≠ KId = sKId
  SubstKC≠ (KLet e) = sKLet (λ x → SubstK≠ (e x))

lemma-SubstK₂-KVar : {var : typK → Set} {τ₁ τ₂ τ₃ : typK}
                     (e : termK[ var , K τ₂ ▷ τ₃ ] τ₁) →
                     SubstK₂ e KVar e
lemma-SubstK₂-KVar (Ret KVar v) = sRet sKVar=
lemma-SubstK₂-KVar (Ret (KLet e₂) v) =
  sRet (sKLet (λ x → lemma-SubstK₂-KVar (e₂ x)))
lemma-SubstK₂-KVar (App v w KVar) = sApp sKVar=
lemma-SubstK₂-KVar (App v w (KLet e₂)) =
  sApp (sKLet (λ x → lemma-SubstK₂-KVar (e₂ x)))
lemma-SubstK₂-KVar (Shift2 e KVar) = sShift2 sKVar=
lemma-SubstK₂-KVar (Shift2 e (KLet e₂)) =
  sShift2 (sKLet (λ x → lemma-SubstK₂-KVar (e₂ x)))
lemma-SubstK₂-KVar (RetE KVar e) = sRetE sKVar=
lemma-SubstK₂-KVar (RetE (KLet e₂) e) =
  sRetE (sKLet (λ x → lemma-SubstK₂-KVar (e₂ x)))
