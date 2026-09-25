module DSterm where

open import Data.Empty
open import Data.Nat

-- type
data typ : Set where
  Nat          : typ
  _⇒_cps[_,_] : typ → typ → typ → typ → typ

data conttyp : Set where
  _▷_ : typ → typ → conttyp

infix 15 _▷_
infix 17 _⇒_cps[_,_]

-- source term
mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    -- x
    Var   : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    -- n
    Num   : ℕ → value[ var ] Nat
    -- λx.M
    Fun   : {τ₁ τ₂ τ₃ τ₄ : typ} →
            (var τ₂ → term[ var , τ₁ ▷ τ₃ ] τ₄) →
            value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])
    -- S
    Shift : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
            value[ var ] (((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])
                          ⇒ τ₁ cps[ τ₂ , τ₅ ])

  data term[_,_]_ (var : typ → Set) : conttyp → typ → Set where
    Val    : {τ₁ τ₂ : typ} →
             value[ var ] τ₁ →
             term[ var , τ₁ ▷ τ₂ ] τ₂
    NonVal : {τ : typ} {Δ : conttyp} →
             nonvalue[ var , Δ ] τ →
             term[ var , Δ ] τ

  data nonvalue[_,_]_ (var : typ → Set) : conttyp → typ → Set where
    -- M N
    App   : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
            term[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆ →
            term[ var , τ₂ ▷ τ₄ ] τ₅ →
            nonvalue[ var , τ₁ ▷ τ₃ ] τ₆
    -- Sk.M
    Shift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
            (var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → term[ var , τ₄ ▷ τ₄ ] τ₅) →
            nonvalue[ var , τ₁ ▷ τ₂ ] τ₅
    -- <M>
    Reset : {τ₁ τ₂ τ₃ : typ} →
            term[ var , τ₁ ▷ τ₁ ] τ₂ →
            nonvalue[ var , τ₂ ▷ τ₃ ] τ₃
    -- let x = M in N
    Let   : {τ₁ τ₄ τ₅ : typ} {τ₂▷τ₃ : conttyp} →
            term[ var , τ₁ ▷ τ₄ ] τ₅ →                -- M
            (var τ₁ → term[ var , τ₂▷τ₃ ] τ₄) →    -- λx. N
            nonvalue[ var , τ₂▷τ₃ ] τ₅
            -- τ₂▷τ₃ を τ₂ ▷ τ₃ にすると、のちに embedContT できなくなる

-- outside-in

-- inside-out
data pcontext[_,_,_]_ (var : typ → Set) : conttyp → typ → typ → Set where
  -- []
  Hole  : {τ₁ τ₂ : typ} →
          pcontext[ var , τ₁ ▷ τ₂ , τ₁ ] τ₂
  -- K[[]@M]
  App₁  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {Δ : conttyp} →
          pcontext[ var , Δ , τ₁ ] τ₃ →
          term[ var , τ₂ ▷ τ₄ ] τ₅ →
          pcontext[ var , Δ , τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] ] τ₅
  -- K[V@[]]
  App₂  : {τ₁ τ₂ τ₃ τ₄ : typ} {Δ : conttyp} →
          value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) →
          pcontext[ var , Δ , τ₁ ] τ₃ →
          pcontext[ var , Δ , τ₂ ] τ₄
  -- K[Let x = [] in M]
  Let   : {τ₁ τ₂ τ₃ τ₄ : typ} {Δ : conttyp} →
          pcontext[ var , Δ , τ₁ ] τ₃ →                -- K
          (var τ₂ → term[ var , τ₁ ▷ τ₃ ] τ₄) →        -- λx. M
          pcontext[ var , Δ , τ₂ ] τ₄

plug : {var : typ → Set} → {τ₁ τ₂ τ₃ : typ} {τ₄▷τ₅ : conttyp} →
       pcontext[ var , τ₄▷τ₅ , τ₁ ] τ₂ →
       term[ var , τ₁ ▷ τ₂ ] τ₃ →
       term[ var , τ₄▷τ₅ ] τ₃
plug Hole e = e
plug (App₁ k e₂) e = plug k (NonVal (App e e₂))
plug (App₂ v₁ k) e = plug k (NonVal (App (Val v₁) e))
plug (Let k e₂) e = plug k (NonVal (Let e e₂))

-- examples
-- λx.x
val1 : {var : typ → Set} → {τ₁ τ₂ : typ} →
       value[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val1 = Fun (λ x → Val (Var x))

-- λx.S(λk.k x)
val2 : {var : typ → Set} → {τ₁ τ₂ : typ} →
       value[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val2 = Fun (λ x → NonVal (App (Val Shift)
         (Val (Fun (λ k → NonVal (App (Val (Var k)) (Val (Var x))))))))

val2' : {var : typ → Set} → {τ₁ τ₂ : typ} →
        value[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val2' = Fun (λ x → NonVal (Shift2 (λ k →
          NonVal (App (Val (Var k)) (Val (Var x))))))

-- λx.S(λk.x)
val3 : {var : typ → Set} → {τ₁ τ₂ τ₃ τ : typ} →
       value[ var ] (τ₁ ⇒ τ₂ cps[ τ₃ , τ₁ ])
val3 {τ = τ} = Fun (λ x → NonVal (App (Val (Shift {τ₃ = τ}))
                                        (Val (Fun (λ k → Val (Var x))))))

val3' : {var : typ → Set} → {τ₁ τ₂ τ₃ τ : typ} →
        value[ var ] (τ₁ ⇒ τ₂ cps[ τ₃ , τ₁ ])
val3' {τ = τ} = Fun (λ x → NonVal (Shift2 {τ₃ = τ} (λ k → Val (Var x))))

-- λxyzw. (x y) (z w)
val4 : {var : typ → Set} → {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ τ₁₀ τ₁₁ : typ} →
       value[ var ]
        ((τ₁ ⇒ (τ₂ ⇒ τ₃ cps[ τ₄ , τ₅ ]) cps[ τ₆ , τ₇ ]) ⇒
         (τ₁ ⇒ ((τ₈ ⇒ τ₂ cps[ τ₅ , τ₆ ]) ⇒ (τ₈ ⇒ τ₃ cps[ τ₄ , τ₇ ])
                 cps[ τ₉ , τ₉ ]) cps[ τ₁₀ , τ₁₀ ])
         cps[ τ₁₁ , τ₁₁ ])
val4 = Fun (λ x → Val (Fun (λ y → Val (Fun (λ z → Val (Fun (λ w →
         NonVal (App (NonVal (App (Val (Var x)) (Val (Var y))))
                     (NonVal (App (Val (Var z)) (Val (Var w))))))))))))

-- λxyzw. let m = x y in let n = z w in m n
val4' : {var : typ → Set} → {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ τ₁₀ τ₁₁ : typ} →
       value[ var ]
        ((τ₁ ⇒ (τ₂ ⇒ τ₃ cps[ τ₄ , τ₅ ]) cps[ τ₆ , τ₇ ]) ⇒
         (τ₁ ⇒ ((τ₈ ⇒ τ₂ cps[ τ₅ , τ₆ ]) ⇒ (τ₈ ⇒ τ₃ cps[ τ₄ , τ₇ ])
                 cps[ τ₉ , τ₉ ]) cps[ τ₁₀ , τ₁₀ ])
         cps[ τ₁₁ , τ₁₁ ])
val4' = Fun (λ x → Val (Fun (λ y → Val (Fun (λ z → Val (Fun (λ w →
          NonVal (Let (NonVal (App (Val (Var x)) (Val (Var y)))) (λ m →
            NonVal (Let (NonVal (App (Val (Var z)) (Val (Var w)))) (λ n →
              NonVal (App (Val (Var m)) (Val (Var n))))))))))))))

-- λxyzw. let m = x y in let n = z w in m n
val4'' : {var : typ → Set} → {τ₁ τ₂ τ₃ τ₅ τ₆ τ₇ τ₈ τ₉ τ₁₀ τ₁₁ : typ} →
         -- τ₃ = τ₄
       value[ var ]
        ((τ₁ ⇒ (τ₂ ⇒ τ₃ cps[ τ₃ , τ₅ ]) cps[ τ₆ , τ₇ ]) ⇒
         (τ₁ ⇒ ((τ₈ ⇒ τ₂ cps[ τ₅ , τ₆ ]) ⇒ (τ₈ ⇒ τ₃ cps[ τ₃ , τ₇ ])
                 cps[ τ₉ , τ₉ ]) cps[ τ₁₀ , τ₁₀ ])
         cps[ τ₁₁ , τ₁₁ ])
val4'' = Fun (λ x → Val (Fun (λ y → Val (Fun (λ z → Val (Fun (λ w →
               plug (Let Hole (λ m →
                      plug (Let Hole (λ n →
                             plug Hole
                               (NonVal (App (Val (Var m)) (Val (Var n))))))
                        (NonVal (App (Val (Var z)) (Val (Var w))))))
                 (NonVal (App (Val (Var x)) (Val (Var y)))))))))))

{- KNormal:
Fun (λ x → Ret KVar
  (Fun (λ y → Ret KVar
    (Fun (λ z → Ret KVar
      (Fun (λ w →
        App (Var x) (Var y)
            (KLet (λ m →
              App (Var z) (Var w)
                  (KLet (λ n → App (Var m) (Var n) KVar)))))))))))
-}

-- λx.λy.y ((λz.z) x)
val5 : {var : typ → Set} → {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
       value[ var ]
       (τ₁ ⇒ ((τ₁ ⇒ τ₂ cps[ τ₃ , τ₄ ]) ⇒ τ₂ cps[ τ₃ , τ₄ ])
        cps[ τ₅ , τ₅ ])
val5 = Fun (λ x → Val (Fun (λ y →
         NonVal (App (Val (Var y))
                     (NonVal (App (Val (Fun (λ z → Val (Var z))))
                                  (Val (Var x))))))))

-- interpreter
〚_〛 : typ → Set
〚 Nat 〛 = ℕ
〚 τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] 〛 =
   〚 τ₂ 〛 → (〚 τ₁ 〛 → 〚 τ₃ 〛) → 〚 τ₄ 〛

mutual
  gv : {τ : typ} → value[ 〚_〛 ] τ → 〚 τ 〛
  gv (Var x) = x
  gv (Num n) = n
  gv (Fun e) = λ x k → g (e x) k
  gv Shift = λ v k → v (λ x₂ k₂ → k₂ (k x₂)) (λ x → x)

  g : {τ₁ τ₂ τ₃ : typ} →
      term[ 〚_〛 , τ₁ ▷ τ₂ ] τ₃ → (〚 τ₁ 〛 → 〚 τ₂ 〛) → 〚 τ₃ 〛
  g (Val v) k = k (gv v)
  g (NonVal e) k = gp e k

  gp : {τ₁ τ₂ τ₃ : typ} →
       nonvalue[ 〚_〛 , τ₁ ▷ τ₂ ] τ₃ → (〚 τ₁ 〛 → 〚 τ₂ 〛) → 〚 τ₃ 〛
  gp (App e₁ e₂) k = g e₁ (λ v₁ → g e₂ (λ v₂ → v₁ v₂ k))
  gp (Shift2 e) k = g (e (λ x₂ k₂ → k₂ (k x₂))) (λ x → x)
  gp (Reset e) k = k (g e (λ x → x))
  gp (Let e₁ e₂) k = g e₁ (λ v₁ → g (e₂ v₁) k)

-- M[x:=V]
-- substitution relation
mutual
  data SubstV {var : typ → Set} : {τ₁ τ₂ : typ} →
              (var τ₁ → value[ var ] τ₂) →
              value[ var ] τ₁ →
              value[ var ] τ₂ → Set where
    -- (λx.x)[v] → v
    sVar=  : {τ₁ : typ} {v : value[ var ] τ₁} →
             SubstV (λ x → Var x) v v
    -- (λ_.x)[v] → x
    sVar≠  : {τ₁ τ₂ : typ} {v : value[ var ] τ₂} {x : var τ₁} →
             SubstV (λ _ → Var x) v (Var x)
    -- (λ_.n)[v] → n
    sNum   : {τ₁ : typ} {v : value[ var ] τ₁} {n : ℕ} →
             SubstV (λ _ → Num n) v (Num n)
    -- (λy.λx.ey)[v] → λx.e′
    sFun   : {τ τ₁ τ₂ τ₃ τ₄ : typ} →
             {e₁ : var τ₁ → var τ → term[ var , τ₂ ▷ τ₃ ] τ₄} →
             {v : value[ var ] τ₁} →
             {e₁′ : var τ → term[ var , τ₂ ▷ τ₃ ] τ₄} →
             ((x : var τ) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
             SubstV (λ y → Fun (e₁ y)) v (Fun e₁′)
    -- (λ_.S)[v] → S
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {v : value[ var ] τ} →
             SubstV (λ _ → Shift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅}) v Shift

  data Subst {var : typ → Set} : {τ₁ τ₂ : typ} {Δ : conttyp} →
             (var τ₁ → term[ var , Δ ] τ₂) →
             value[ var ] τ₁ →
             term[ var , Δ ] τ₂ → Set where
    sVal   : {τ τ₁ τ₂ : typ} →
             {v₁ : var τ → value[ var ] τ₁} →
             {v : value[ var ] τ} →
             {v₁′ : value[ var ] τ₁} →
             SubstV v₁ v v₁′ →
             Subst {τ₂ = τ₂} (λ y → Val (v₁ y)) v (Val v₁′)
    sNonVal : {τ τ₄ : typ} {τ₁▷τ₃ : conttyp} →
             {e : var τ → nonvalue[ var , τ₁▷τ₃ ] τ₄} →
             {v : value[ var ] τ} →
             {e′ : nonvalue[ var , τ₁▷τ₃ ] τ₄} →
             SubstNV e v e′ →
             Subst (λ y → NonVal (e y)) v (NonVal e′)

  data SubstNV {var : typ → Set} : {τ₁ τ₄ : typ} {τ₂▷τ₃ : conttyp} →
             (var τ₁ → nonvalue[ var , τ₂▷τ₃ ] τ₄) →
             value[ var ] τ₁ →
             nonvalue[ var , τ₂▷τ₃ ] τ₄ → Set where
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
             {e₁ : var τ → term[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆}
             {e₂ : var τ → term[ var , τ₂ ▷ τ₄ ] τ₅}
             {v : value[ var ] τ}
             {e₁′ : term[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆}
             {e₂′ : term[ var , τ₂ ▷ τ₄ ] τ₅} →
             Subst e₁ v e₁′ → Subst e₂ v e₂′ →
             SubstNV (λ y → App (e₁ y) (e₂ y)) v (App e₁′ e₂′)
    sShift2 : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
             {e : var τ₁ →
                  var (τ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → term[ var , τ₄ ▷ τ₄ ] τ₅} →
             {v : value[ var ] τ₁} →
             {e′ : var (τ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                   term[ var , τ₄ ▷ τ₄ ] τ₅} →
             ((x : var (τ ⇒ τ₂ cps[ τ₃ , τ₃ ])) →
              Subst (λ y → (e y) x) v (e′ x)) →
             SubstNV (λ y → Shift2 (e y)) v (Shift2 e′)
    sReset : {τ τ₁ τ₂ τ₄ : typ} →
             {e₁ : var τ → term[ var , τ₁ ▷ τ₁ ] τ₂} →
             {v : value[ var ] τ} →
             {e₁′ : term[ var , τ₁ ▷ τ₁ ] τ₂} →
             Subst e₁ v e₁′ →
             SubstNV {τ₄ = τ₄} (λ y → Reset (e₁ y))
                     v
                     (Reset e₁′)
    sLet   : {τ τ₁ β γ : typ} {τ₂▷α : conttyp} →
             {e₁ : var τ → term[ var , τ₁ ▷ β ] γ} →
             {e₂ : var τ → (var τ₁ → term[ var , τ₂▷α ] β)} →
             {v : value[ var ] τ} →
             {e₁′ : term[ var , τ₁ ▷ β ] γ} →
             {e₂′ : var τ₁ → term[ var , τ₂▷α ] β} →
             ((x : var τ₁) → Subst (λ y → (e₂ y) x) v (e₂′ x)) →
             Subst e₁ v e₁′ →
             SubstNV (λ y → Let (e₁ y) (e₂ y)) v (Let e₁′ e₂′)

data SubstC  {var : typ → Set} : {τ₁ τ₂ τ₃ : typ} {Δ : conttyp} →
             (var τ₁ → pcontext[ var , Δ , τ₃ ] τ₂) →
             value[ var ] τ₁ →
             pcontext[ var , Δ , τ₃ ] τ₂ → Set where

  sHole  :  {τ₁ τ₂ τ₃ : typ} →
            {v : value[ var ] τ₁} →
            SubstC {τ₂ = τ₂}{τ₃ = τ₃} (λ x → Hole) v Hole

  sApp₁  :  {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ : typ} →
            {c₁ : var τ₁ → pcontext[ var , τ₆ ▷ τ₇ , τ₁ ] τ₃} →
            {c₂ : pcontext[ var , τ₆ ▷ τ₇ , τ₁ ] τ₃} →
            {e₁ : var τ₁ → term[ var , τ₂ ▷ τ₄ ] τ₅} →
            {e₂ : term[ var , τ₂ ▷ τ₄ ] τ₅} →
            {v : value[ var ] τ₁} →
            Subst e₁ v e₂ →
            SubstC c₁ v c₂ →
            SubstC (λ x → App₁ (c₁ x) (e₁ x)) v (App₁ c₂ e₂)

  sApp₂  :  {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
            {v₁ : var τ₁ → value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
            {v₂ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
            {c₁ : var τ₁ → pcontext[ var , τ₅ ▷ τ₆ , τ₁ ] τ₃} →
            {c₂ : pcontext[ var , τ₅ ▷ τ₆ , τ₁ ] τ₃} →
            {v : value[ var ] τ₁} →
            SubstV v₁ v v₂ →
            SubstC c₁ v c₂ →
            SubstC (λ x → App₂ (v₁ x) (c₁ x)) v (App₂ v₂ c₂)

  sLet   :  {τ τ₁ τ₂ τ₃ τ₄ : typ} {Δ : conttyp} →
            {c₁ : var τ → pcontext[ var , Δ , τ₁ ] τ₃} →
            {c₂ : pcontext[ var , Δ , τ₁ ] τ₃} →
            {e₁ : var τ → (var τ₂ → (term[ var , τ₁ ▷ τ₃ ] τ₄))} →
            {e₂ : var τ₂ → term[ var , τ₁ ▷ τ₃ ] τ₄} →
            {v : value[ var ] τ} →
            SubstC c₁ v c₂ →
            ((x : var τ₂) → Subst (λ y → e₁ y x) v (e₂ x)) →
            SubstC (λ x → Let (c₁ x) (λ y → e₁ x y)) v (Let c₂ (λ y → e₂ y))

mutual
  SubstV≠ : {var : typ → Set} {τ₁ τ : typ} →
            (v₁ : value[ var ] τ₁) →
            {v : value[ var ] τ} →
            SubstV (λ y → v₁) v v₁
  SubstV≠ (Var x) = sVar≠
  SubstV≠ (Num n) = sNum
  SubstV≠ (Fun e) = sFun (λ x → Subst≠ (e x))
  SubstV≠ Shift = sShift

  Subst≠ : {var : typ → Set} {τ τ₄ : typ} {τ₁▷τ₃ : conttyp} →
           (e : term[ var , τ₁▷τ₃ ] τ₄) →
           {v : value[ var ] τ} →
           Subst (λ y → e) v e
  Subst≠ (Val v) = sVal (SubstV≠ v)
  Subst≠ (NonVal e) = sNonVal (SubstNV≠ e)

  SubstNV≠ : {var : typ → Set} {τ τ₄ : typ} {τ₁▷τ₃ : conttyp} →
             (e : nonvalue[ var , τ₁▷τ₃ ] τ₄) →
             {v : value[ var ] τ} →
             SubstNV (λ y → e) v e
  SubstNV≠ (App (Val v₁) (Val v₂)) =
    sApp (sVal (SubstV≠ v₁)) (sVal (SubstV≠ v₂))
  SubstNV≠ (App (Val v₁) (NonVal e₂)) =
    sApp (sVal (SubstV≠ v₁)) (sNonVal (SubstNV≠ e₂))
  SubstNV≠ (App (NonVal e₁) (Val v₂)) =
    sApp (sNonVal (SubstNV≠ e₁)) (sVal (SubstV≠ v₂))
  SubstNV≠ (App (NonVal e₁) (NonVal e₂)) =
    sApp (sNonVal (SubstNV≠ e₁)) (sNonVal (SubstNV≠ e₂))
  SubstNV≠ (Shift2 e) = sShift2 (λ k → Subst≠ (e k))
  SubstNV≠ (Reset e) = sReset (Subst≠ e)
  SubstNV≠ (Let e₁ e₂) = sLet (λ x → Subst≠ (e₂ x)) (Subst≠ e₁)

-- reduction rules
data Reduce {var : typ → Set} : {β : typ} {τ▷α : conttyp} →
            term[ var , τ▷α ] β →
            term[ var , τ▷α ] β → Set where
  -- (λx.M)V -> M[x:=V]
  RBetaV : {τ τ₁ τ₂ τ₃ : typ} →
           (e₁ : var τ → term[ var , τ₁ ▷ τ₂ ] τ₃) →
           (v₂ : value[ var ] τ) →
           (e₁′ : term[ var , τ₁ ▷ τ₂ ] τ₃) →
           (sub : Subst e₁ v₂ e₁′) →
           Reduce (NonVal (App (Val (Fun e₁)) (Val v₂)))
                  e₁′
  -- λx.V@x -> V
  REtaV  : {τ₁ τ₂ τ₃ τ₄ β : typ} →
           (v : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])) →
           Reduce {β = β}
                  (Val (Fun (λ x → NonVal (App (Val v) (Val (Var x))))))
                  (Val v)
  -- let x = V in M -> M[x:=V]
  RBetaLet : {τ₁ τ₄ : typ} {τ₂▷τ₃ : conttyp} →
           (v₁ : value[ var ] τ₁) →
           (e₂ : var τ₁ → term[ var , τ₂▷τ₃ ] τ₄) →
           (e₂′ : term[ var , τ₂▷τ₃ ] τ₄) →
           (sub : Subst e₂ v₁ e₂′) →
           Reduce (NonVal (Let (Val v₁) e₂))
                  e₂′
  -- let x = M in x -> M
  REtaLet : {τ₁ τ₂ τ₃ : typ} →
           (e₁ : term[ var , τ₁ ▷ τ₂ ] τ₃) →
           Reduce (NonVal (Let e₁ (λ x → Val (Var x))))
                  e₁
  -- let y = (let x = L in M) in N -> let x = L in let y = M in N
  RAssoc : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {τ₇▷τ₈ : conttyp} →
           (e₁ : term[ var , τ₁ ▷ τ₂ ] τ₃) →
           (e₂ : var τ₁ → term[ var , τ₄ ▷ τ₅ ] τ₂) →
           (e₃ : var τ₄ → term[ var , τ₇▷τ₈ ] τ₅) →
           Reduce (NonVal (Let (NonVal (Let e₁ (λ x → e₂ x))) (λ y → e₃ y)))
                  (NonVal (Let e₁ (λ x → NonVal (Let (e₂ x) (λ y → e₃ y)))))
  -- P@N -> let x = P in x@N
  RLet1  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
           (e₁ : nonvalue[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆) →
           (e₂ : term[ var , τ₂ ▷ τ₄ ] τ₅) →
           Reduce (NonVal (App (NonVal e₁) e₂))
                  (NonVal (Let (NonVal e₁) (λ x →
                            NonVal (App (Val (Var x)) e₂))))
  -- V@Q -> let y = Q in V@y
  RLet2  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
           {v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
           (e₂ : nonvalue[ var , τ₂ ▷ τ₄ ] τ₅) →
           Reduce (NonVal (App (Val v₁) (NonVal e₂)))
                  (NonVal (Let (NonVal e₂) (λ y →
                            NonVal (App (Val v₁) (Val (Var y))))))
  -- <J[S@V]> -> <V@(λy.<J[y]>)>
  RShift : {τ₁ τ₂ τ₃ τ₄ τ₅ β : typ} →
           (v : value[ var ]
                ((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])
               ) →
           (j : pcontext[ var , τ₄ ▷ τ₄ , τ₁ ] τ₂) →
           Reduce {β = β}
                  (NonVal (Reset (plug j (NonVal (App (Val Shift) (Val v))))))
                  (NonVal (Reset (NonVal (App (Val v)
                    (Val (Fun (λ y →
                      NonVal (Reset (plug j (Val (Var y)))))))))))
  -- <J[Sk.M]> -> <(λk.M)@(λy.<J[y]>)>
  RShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ β : typ} →
           (e : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → term[ var , τ₄ ▷ τ₄ ] τ₅) →
           (j : pcontext[ var , τ₄ ▷ τ₄ , τ₁ ] τ₂) →
           Reduce {β = β}
                  (NonVal (Reset (plug j (NonVal (Shift2 e)))))
                  (NonVal (Reset (NonVal (App (Val (Fun e))
                    (Val (Fun (λ y →
                      NonVal (Reset (plug j (Val (Var y)))))))))))
  -- <V> -> V
  RReset : {τ₁ β : typ} →
           (v₁ : value[ var ] τ₁) →
           Reduce {β = β} (NonVal (Reset (Val v₁))) (Val v₁)

  -- congruence rules
  RFun   : {τ₁ τ₂ τ₃ τ₄ β : typ} →
           {e e′ : var τ₂ → term[ var , τ₁ ▷ τ₃ ] τ₄} →
           ((x : var τ₂) → Reduce (e x) (e′ x)) →
           Reduce {β = β} (Val (Fun e)) (Val (Fun e′))
  RApp₁  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
           {e₁ e₁′ : term[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆} →
           {e₂ : term[ var , τ₂ ▷ τ₄ ] τ₅} →
           Reduce e₁ e₁′ →
           Reduce (NonVal (App e₁ e₂)) (NonVal (App e₁′ e₂))
  RApp₂  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
           {v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
           {e₂ e₂′ : term[ var , τ₂ ▷ τ₄ ] τ₅} →
           Reduce e₂ e₂′ →
           Reduce (NonVal (App (Val v₁) e₂)) (NonVal (App (Val v₁) e₂′))
  RLet₁  : {τ₁ β γ : typ} {τ₂▷α : conttyp} →
           {e₁ e₁′ : term[ var , τ₁ ▷ β ] γ} →
           {e₂ : (var τ₁ → term[ var , τ₂▷α ] β)} →
           Reduce e₁ e₁′ →
           Reduce (NonVal (Let e₁ e₂)) (NonVal (Let e₁′ e₂))
  RLet₂  : {τ₁ β γ : typ} {τ₂▷α : conttyp} →
           {e₁ : term[ var , τ₁ ▷ β ] γ} →
           {e₂ e₂′ : (var τ₁ → term[ var , τ₂▷α ] β)} →
           ((x : var τ₁) → Reduce (e₂ x) (e₂′ x)) →
           Reduce (NonVal (Let e₁ e₂)) (NonVal (Let e₁ e₂′))
  RShift₁ : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
           {e e′ : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                   term[ var , τ₄ ▷ τ₄ ] τ₅} →
           ((x : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ])) → Reduce (e x) (e′ x)) →
           Reduce (NonVal (Shift2 e))
                  (NonVal (Shift2 e′))
  RReset₁ : {τ₁ τ₂ β : typ} →
           {e e′ : term[ var , τ₁ ▷ τ₁ ] τ₂} →
           Reduce e e′ →
           Reduce {β = β}
                  (NonVal (Reset e))
                  (NonVal (Reset e′))
  -- closure rules
  RId    : {β : typ} {τ▷α : conttyp } →
           {e : term[ var , τ▷α ] β} →
           Reduce e e
  RTrans : {β : typ} {τ▷α : conttyp } →
           {e₁ e₂ e₃ : term[ var , τ▷α ] β} →
           Reduce e₁ e₂ →
           Reduce e₂ e₃ →
           Reduce e₁ e₃

-- equational reasoning
open import Relation.Binary.PropositionalEquality

module Reasoning where

  infix  3 _∎
  infixr 2 _⟶⟨_⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : {var : typ → Set} {τ₃ : typ} {τ₁▷τ₂ : conttyp} →
           {e₁ e₂ : term[ var , τ₁▷τ₂ ] τ₃} →
           Reduce e₁ e₂ → Reduce e₁ e₂
  begin_ red = red

  _⟶⟨_⟩_ : {var : typ → Set} {τ₃ : typ} {τ₁▷τ₂ : conttyp} →
            (e₁ {e₂ e₃} : term[ var , τ₁▷τ₂ ] τ₃) →
            Reduce e₁ e₂ → Reduce e₂ e₃ → Reduce e₁ e₃
  _⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red-e₃ = RTrans e₁-red-e₂ e₂-red-e₃

  _≡⟨_⟩_ : {var : typ → Set} {τ₃ : typ} {τ₁▷τ₂ : conttyp} →
           (e₁ {e₂ e₃} : term[ var , τ₁▷τ₂ ] τ₃) →
           e₁ ≡ e₂ → Reduce e₂ e₃ →
           Reduce e₁ e₃
  _≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red-e₃ = e₂-red-e₃

  _∎ : {var : typ → Set} {τ₃ : typ} {τ₁▷τ₂ : conttyp} →
       (e : term[ var , τ₁▷τ₂ ] τ₃) → Reduce e e
  _∎ e = RId

-- lemma

-- v does not reduce to nonval e
reduceVal : {var : typ → Set} {τ₁ τ₂ : typ}
            {v : value[ var ] τ₁}
            {e : nonvalue[ var , τ₁ ▷ τ₂ ] τ₂} →
            Reduce (Val v) (NonVal e) → ⊥
reduceVal (RTrans {e₂ = Val v} red₁ red₂) = reduceVal red₂
reduceVal (RTrans {e₂ = NonVal e} red₁ red₂) = reduceVal red₁

-- e -> e' => K[e] -> K[e']
reducePlug : {var : typ → Set} {τ₁ τ₂ τ₃ : typ} {τ₄▷τ₅ : conttyp}
             (k : pcontext[ var , τ₄▷τ₅ , τ₁ ] τ₂) →
             {e e' : term[ var , τ₁ ▷ τ₂ ] τ₃} →
             Reduce e e' →
             Reduce (plug k e) (plug k e')
reducePlug Hole red = red
reducePlug (App₁ k e₂) red = reducePlug k (RApp₁ red)
reducePlug (App₂ v₁ k) red = reducePlug k (RApp₂ red)
reducePlug (Let k e₂) red = reducePlug k (RLet₁ red)

-- (K[e])[v] = K[v][e[v]]
substPlug : {var : typ → Set} {τ₃ τ₄ τ₅ τ₆ : typ} {Δ : conttyp}
            {k : var τ₄ → pcontext[ var , Δ , τ₅ ] τ₃} →
            {k′ : pcontext[ var , Δ , τ₅ ] τ₃} →
            {v : value[ var ] τ₄} →
            {e : var τ₄ → term[ var , τ₅ ▷ τ₃ ] τ₆} →
            {e′ : term[ var , τ₅ ▷ τ₃ ] τ₆} →
            SubstC k v k′ →
            Subst (λ x → e x) v e′ →
            Subst (λ x → plug (k x) (e x)) v (plug k′ e′)
substPlug sHole sub = sub
substPlug (sApp₁ sub₁ subC) sub₂ = substPlug subC (sNonVal (sApp sub₂ sub₁))
substPlug (sApp₂ subV subC) sub =
  substPlug  subC (sNonVal (sApp (sVal subV) sub))
substPlug (sLet subC sub₁) sub₂ =
  substPlug subC (sNonVal (sLet (λ x → sub₁ x) sub₂))
