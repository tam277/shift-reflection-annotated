module CPSterm where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- target type
mutual
  data cpstyp : Set where
    Nat : cpstyp
    _⇒[_⇒_]⇒_ : cpstyp → cpstyp → cpstyp → cpstyp → cpstyp

  data conttyp : Set where
    K_⇒_ : cpstyp → cpstyp → conttyp
    •_ : cpstyp → conttyp

Δ-cpstype : conttyp → cpstyp → cpstyp → Set
Δ-cpstype (K τ₁′ ⇒ τ₂′) τ₁ τ₂ = τ₁′ ≡ τ₁ × τ₂′ ≡ τ₂
Δ-cpstype (• τ) τ₁ τ₂ = τ ≡ τ₁ × τ ≡ τ₂

-- CPS terms
mutual
  data cpsvalue[_]_ (var : cpstyp → Set) : cpstyp → Set where
    -- x
    CPSVar : {τ₁ : cpstyp} → (x : var τ₁) → cpsvalue[ var ] τ₁
    -- n
    CPSNum : (n : ℕ) → cpsvalue[ var ] Nat
    -- λx.λk.M
    CPSFun : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             (e : var τ₂ → cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄) →
             cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
    -- S
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             cpsvalue[ var ]
             (((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)
              ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)

  data cpsterm[_,_]_ (var : cpstyp → Set) : conttyp → cpstyp → Set where
    -- K V
    CPSRet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
             (k : cpscont[ var , Δ , τ₁ ] τ₂) →
             (v : cpsvalue[ var ] τ₁) →
             cpsterm[ var , Δ ] τ₂
    -- V W K
    CPSApp : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
             (v : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)) →
             (w : cpsvalue[ var ] τ₂) →
             (k : cpscont[ var , Δ , τ₁ ] τ₃) →
             cpsterm[ var , Δ ] τ₄
    -- (Sk.M) K
    CPSShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} → {Δ : conttyp} →
             (e : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                  cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅) →
             (k : cpscont[ var , Δ , τ₁ ] τ₂) →
             cpsterm[ var , Δ ] τ₅
    -- K M
    CPSRetE : {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
             (k : cpscont[ var , Δ , τ₁ ] τ₂) →
             (e : cpsterm[ var , • τ ] τ₁) →
             cpsterm[ var , Δ ] τ₂

  data cpscont[_,_,_]_ (var : cpstyp → Set) :
       conttyp → cpstyp → cpstyp → Set where
    -- k
    CPSKVar : {τ₁ τ₂ : cpstyp} →
              cpscont[ var , K τ₁ ⇒ τ₂ , τ₁ ] τ₂
    -- λx.x
    CPSKId  : {τ₁ : cpstyp} →
              cpscont[ var , • τ₁ , τ₁ ] τ₁
    -- λx.M
    CPSKLet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
              (e : var τ₁ → cpsterm[ var , Δ ] τ₂) →
              cpscont[ var , Δ , τ₁ ] τ₂

-- example
-- λx.λk.k x
val1 : {var : cpstyp → Set} → {τ₁ τ₂ : cpstyp} →
       cpsvalue[ var ] (τ₁ ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₂)
val1 = CPSFun (λ x → CPSRet CPSKVar (CPSVar x))

-- interpreter
〚_〛 : cpstyp → Set
〚 Nat 〛 = ℕ
〚 τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄ 〛 =
  〚 τ₂ 〛 → (〚 τ₁ 〛 → 〚 τ₃ 〛) → 〚 τ₄ 〛

〚_〛' : conttyp → Set
〚 K τ ⇒ α 〛' = 〚 τ 〛 → 〚 α 〛
〚 • τ 〛' = 〚 τ 〛 → 〚 τ 〛

mutual
  gv : {τ : cpstyp} → cpsvalue[ 〚_〛 ] τ → 〚 τ 〛
  gv (CPSVar x) = x
  gv (CPSNum n) = n
  gv (CPSFun e) = λ x k → g (e x) k
  gv CPSShift = λ v k → v (λ x₂ k₂ → k₂ (k x₂)) (λ x → x)

  g : {τ : cpstyp} → {Δ : conttyp} →
      cpsterm[ 〚_〛 , Δ ] τ → 〚 Δ 〛' → 〚 τ 〛
  g (CPSRet k v) Δ = (gc k Δ) (gv v)
  g (CPSApp v w k) Δ = (gv v) (gv w) (gc k Δ)
  g (CPSShift2 e k) Δ = g (e λ x₂ k₂ → k₂ (gc k Δ x₂)) (λ x → x)
  g (CPSRetE k e) Δ = (gc k Δ) (g e (λ x → x))

  gc : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
       cpscont[ 〚_〛 , Δ , τ₁ ] τ₂ → 〚 Δ 〛' →
       〚 τ₁ 〛 → 〚 τ₂ 〛
  gc CPSKVar k = k
  gc CPSKId Δ = λ x → x
  gc (CPSKLet e) Δ = λ x → g (e x) Δ

-- 値による代入規則
mutual
  data cpsSubstV {var : cpstyp → Set} : {τ τ₁ : cpstyp} →
                 (var τ → cpsvalue[ var ] τ₁) →
                 cpsvalue[ var ] τ →
                 cpsvalue[ var ] τ₁ → Set where
    sVar= : {τ : cpstyp} {v : cpsvalue[ var ] τ} →
            cpsSubstV (λ x → CPSVar x) v v
    sVar≠ : {τ τ₁ : cpstyp} {v : cpsvalue[ var ] τ} {x : var τ₁} →
            cpsSubstV (λ _ → CPSVar x) v (CPSVar x)
    sNum  : {τ : cpstyp} {v : cpsvalue[ var ] τ} {n : ℕ} →
            cpsSubstV (λ _ → CPSNum n) v (CPSNum n)
    sFun  : {τ′ τ₀ τ₁ τ₃ τ₄ : cpstyp} →
            {e  : var τ′ →  var τ₀ → cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄} →
            {v  : cpsvalue[ var ] τ′} →
            {e′ : var τ₀ → cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄} →
            ((x : var τ₀) → cpsSubst (λ y → (e y) x) v (e′ x)) →
            cpsSubstV (λ y → CPSFun (λ x → (e y) x)) v (CPSFun e′)
    sShift : {τ₁ τ₂ τ₃ τ₄ τ₅ τ : cpstyp} {v : cpsvalue[ var ] τ} →
            cpsSubstV (λ _ → CPSShift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅})
                      v CPSShift

  data cpsSubst {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} {Δ : conttyp} →
                (var τ₁ → cpsterm[ var , Δ ] τ₂) →
                cpsvalue[ var ] τ₁ →
                cpsterm[ var , Δ ] τ₂ → Set where
    sRet  : {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
            {k₁ : var τ → cpscont[ var , Δ , τ₁ ] τ₂} →
            {v₁ : var τ → cpsvalue[ var ] τ₁} →
            {v  : cpsvalue[ var ] τ} →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₂} →
            {v₂ : cpsvalue[ var ] τ₁} →
            cpsSubstC k₁ v k₂ → cpsSubstV v₁ v v₂ →
            cpsSubst (λ y → CPSRet (k₁ y) (v₁ y)) v (CPSRet k₂ v₂)
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
            {v₁ : var τ → cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {w₁ : var τ → cpsvalue[ var ] τ₂ } →
            {k₁ : var τ → cpscont[ var , Δ , τ₁ ] τ₃ } →
            {v  : cpsvalue[ var ] τ } →
            {v₂ : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {w₂ : cpsvalue[ var ] τ₂ } →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₃ } →
            cpsSubstV v₁ v v₂ →
            cpsSubstV w₁ v w₂ →
            cpsSubstC k₁ v k₂ →
            cpsSubst (λ y → CPSApp (v₁ y) (w₁ y) (k₁ y)) v
                     (CPSApp v₂ w₂ k₂)
    sShift2 : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} → {Δ : conttyp} →
            {e₁ : var τ → var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                  cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅} →
            {k₁ : var τ → cpscont[ var , Δ , τ₁ ] τ₂} →
            {v  : cpsvalue[ var ] τ} →
            {e₂ : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                  cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅} →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₂} →
            ((x : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃)) →
             cpsSubst (λ y → (e₁ y) x) v (e₂ x)) →
            cpsSubstC k₁ v k₂ →
            cpsSubst (λ y → (CPSShift2 (e₁ y) (k₁ y))) v (CPSShift2 e₂ k₂)
    sRetE : {τ τ₁ τ₂ α : cpstyp} → {Δ : conttyp} →
            {k₁ : var τ → cpscont[ var , Δ , τ₁ ] τ₂} →
            {e₁ : var τ → cpsterm[ var , • α ] τ₁} →
            {v  : cpsvalue[ var ] τ} →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₂} →
            {e₂ : cpsterm[ var , • α ] τ₁} →
            cpsSubstC k₁ v k₂ → cpsSubst e₁ v e₂ →
            cpsSubst (λ y → CPSRetE (k₁ y) (e₁ y)) v (CPSRetE k₂ e₂)

  data cpsSubstC {var : cpstyp → Set} :
                 {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
                 (var τ → cpscont[ var , Δ , τ₁ ] τ₂) →
                 cpsvalue[ var ] τ →
                 cpscont[ var , Δ , τ₁ ] τ₂ → Set where
    sKVar≠ : {τ τ₁ τ₂ : cpstyp} →
             {v : cpsvalue[ var ] τ} →
             cpsSubstC {τ₁ = τ₁} {τ₂} (λ _ → CPSKVar) v CPSKVar
    sKId   : {τ τ₁ : cpstyp} →
             {v : cpsvalue[ var ] τ} →
             cpsSubstC {τ₁ = τ₁} (λ _ → CPSKId) v CPSKId
    sKLet  : {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
             {e₁ : var τ → var τ₁ → cpsterm[ var , Δ ] τ₂} →
             {v  : cpsvalue[ var ] τ} →
             {e₂ : var τ₁ → cpsterm[ var , Δ ] τ₂ } →
             ((x : var τ₁) → cpsSubst (λ y → (e₁ y) x) v (e₂ x)) →
             cpsSubstC (λ y → CPSKLet (e₁ y)) v (CPSKLet e₂)

-- 継続の代入規則
mutual
  data cpsSubst₂ {var : cpstyp → Set} :
                 {τ₁ α β : cpstyp} → {Δ : conttyp} →
                 cpsterm[ var , K α ⇒ β ] τ₁ → -- has to be K
                 cpscont[ var , Δ , α ] β →
                 cpsterm[ var , Δ ] τ₁ → Set where
    sRet  : {τ₁ τ₂ α β : cpstyp} → {Δ : conttyp} →
            {k₁ : cpscont[ var , K α ⇒ β , τ₁ ] τ₂} →
            {v  : cpsvalue[ var ] τ₁} →
            {c  : cpscont[ var , Δ , α ] β} →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₂} →
            cpsSubstC₂ k₁ c k₂ →
            cpsSubst₂ (CPSRet k₁ v) c (CPSRet k₂ v)
    sApp  : {τ₁ τ₂ τ₃ τ₄ α β : cpstyp} → {Δ : conttyp} →
            {v  : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {w  : cpsvalue[ var ] τ₂ } →
            {k₁ : cpscont[ var , K α ⇒ β , τ₁ ] τ₃ } →
            {c  : cpscont[ var , Δ , α ] β } →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₃ } →
            cpsSubstC₂ k₁ c k₂ →
            cpsSubst₂ (CPSApp v w k₁) c (CPSApp v w k₂)
    sShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ α β : cpstyp} → {Δ : conttyp} →
            {e  : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                  cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅} →
            {k₁ : cpscont[ var , K α ⇒ β , τ₁ ] τ₂} →
            {c  : cpscont[ var , Δ , α ] β} →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₂} →
            cpsSubstC₂ k₁ c k₂ →
            cpsSubst₂ (CPSShift2 e k₁) c (CPSShift2 e k₂)
    sRetE : {τ₁ τ₂ α β γ : cpstyp} → {Δ : conttyp} →
            {k₁ : cpscont[ var , K α ⇒ β , τ₁ ] τ₂} →
            {e  : cpsterm[ var , • γ ] τ₁} →
            {c  : cpscont[ var , Δ , α ] β} →
            {k₂ : cpscont[ var , Δ , τ₁ ] τ₂} →
            cpsSubstC₂ k₁ c k₂ →
            cpsSubst₂ (CPSRetE k₁ e) c (CPSRetE k₂ e)

  data cpsSubstC₂ {var : cpstyp → Set} :
                  {τ₁ τ₂ α β : cpstyp} → {Δ : conttyp} →
                  cpscont[ var , K α ⇒ β , τ₁ ] τ₂ →
                  cpscont[ var , Δ , α ] β →
                  cpscont[ var , Δ , τ₁ ] τ₂ → Set where
    sKVar= : {α β : cpstyp} {Δ : conttyp} →
             {c : cpscont[ var , Δ , α ] β} →
             cpsSubstC₂ CPSKVar c c
    sKLet  : {τ₁ τ₂ α β : cpstyp} → {Δ : conttyp} →
             {e₁ : var τ₁ → cpsterm[ var , K α ⇒ β ] τ₂} →
             {c  : cpscont[ var , Δ , α ] β} →
             {e₂ : var τ₁ → cpsterm[ var , Δ ] τ₂} →
             ((x : var τ₁) → cpsSubst₂ (e₁ x) c (e₂ x)) →
             cpsSubstC₂ (CPSKLet e₁) c (CPSKLet e₂)

--reduction rules
mutual
  data cpsReduce {var : cpstyp → Set} :
                 {τ₁ : cpstyp} → {Δ : conttyp} →
                 cpsterm[ var , Δ ] τ₁ →
                 cpsterm[ var , Δ ] τ₁ → Set where
     -- (λx.λk.M) V K -> M[x:=V][k:=K]
     RBetaV  : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
               {e₁ : var τ₂ → cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄} →
               {v : cpsvalue[ var ] τ₂} →
               {c : cpscont[ var , Δ , τ₁ ] τ₃} →
               {e₁′ : cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄} →
               {e₂ : cpsterm[ var , Δ ] τ₄} →
               cpsSubst e₁ v e₁′ →
               cpsSubst₂ e₁′ c e₂ →
               cpsReduce (CPSApp (CPSFun (λ x → e₁ x)) v c)
                         e₂
     -- (λx.M) V -> M[x:=V]
     RBetaLet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {e : var τ₁ → cpsterm[ var , Δ ] τ₂} →
               {v : cpsvalue[ var ] τ₁} →
               {e′ : cpsterm[ var , Δ ] τ₂} →
               cpsSubst e v e′ →
               cpsReduce (CPSRet (CPSKLet e) v) e′
     -- K (S@V@J) -> K (V@(λy.λk.k@(J@y))@(λx.x))
     RShift  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : cpstyp} → {Δ : conttyp} →
               {v : cpsvalue[ var ]
                    ((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)} →
               {j : cpscont[ var , • τ₄ , τ₁ ] τ₂} →
               {k : cpscont[ var , Δ , τ₅ ] τ₆} →
               cpsReduce (CPSRetE k (CPSApp CPSShift v j))
                         (CPSRetE k (CPSApp v
                                       (CPSFun (λ y →
                                         CPSRetE CPSKVar (CPSRet j (CPSVar y))))
                                       CPSKId))
     -- K (S@V@J) -> K (V@(λy.λk.k@(J@y))@(λx.x))
     RShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : cpstyp} → {Δ : conttyp} →
               {e : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                    cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅} →
               {j : cpscont[ var , • τ₄ , τ₁ ] τ₂} →
               {k : cpscont[ var , Δ , τ₅ ] τ₆} →
               cpsReduce (CPSRetE k (CPSShift2 e j))
                         (CPSRetE k (CPSApp (CPSFun e)
                                       (CPSFun (λ y →
                                         CPSRetE CPSKVar (CPSRet j (CPSVar y))))
                                       CPSKId))
     -- K ((λx.x) V) -> K V
     RReset  : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {v : cpsvalue[ var ] τ₁} →
               {k : cpscont[ var , Δ , τ₁ ] τ₂} →
               cpsReduce (CPSRetE k (CPSRet CPSKId v))
                         (CPSRet k v)

     -- congruence rules
     RRet₁   : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {k k' : cpscont[ var , Δ , τ₁ ] τ₂} →
               {v : cpsvalue[ var ] τ₁} →
               cpsReduceC k k' →
               cpsReduce (CPSRet k v)
                         (CPSRet k' v)
     RRet₂   : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {k : cpscont[ var , Δ , τ₁ ] τ₂} →
               {v v' : cpsvalue[ var ] τ₁} →
               cpsReduceV v v' →
               cpsReduce (CPSRet k v)
                         (CPSRet k v')
     RApp₁   : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
               {v v' : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)} →
               {w : cpsvalue[ var ] τ₂} →
               {k : cpscont[ var , Δ , τ₁ ] τ₃} →
               cpsReduceV v v' →
               cpsReduce (CPSApp v w k)
                         (CPSApp v' w k)
     RApp₂   : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
               {v : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)} →
               {w w' : cpsvalue[ var ] τ₂} →
               {k : cpscont[ var , Δ , τ₁ ] τ₃} →
               cpsReduceV w w' →
               cpsReduce (CPSApp v w k)
                         (CPSApp v w' k)
     RApp₃   : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
               {v : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)} →
               {w : cpsvalue[ var ] τ₂} →
               {k k' : cpscont[ var , Δ , τ₁ ] τ₃} →
               cpsReduceC k k' →
               cpsReduce (CPSApp v w k)
                         (CPSApp v w k')
     RShift₁  : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} → {Δ : conttyp} →
               {k k' : cpscont[ var , Δ , τ₁ ] τ₂} →
               {e : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                        cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅} →
               cpsReduceC k k' →
               cpsReduce (CPSShift2 e k) (CPSShift2 e k')
     RShift₂  : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} → {Δ : conttyp} →
               {k : cpscont[ var , Δ , τ₁ ] τ₂} →
               {e e' : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                       cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅} →
               ((x : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃)) →
               cpsReduce (e x) (e' x)) →
               cpsReduce (CPSShift2 e k) (CPSShift2 e' k)
     RRetE₁  : {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {k k' : cpscont[ var , Δ , τ₁ ] τ₂} →
               {e : cpsterm[ var , • τ ] τ₁} →
               cpsReduceC k k' →
               cpsReduce (CPSRetE k e)
                         (CPSRetE k' e)
     RRetE₂  : {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {k : cpscont[ var , Δ , τ₁ ] τ₂} →
               {e e' : cpsterm[ var , • τ ] τ₁} →
               cpsReduce e e' →
               cpsReduce (CPSRetE k e)
                         (CPSRetE k e')
     -- closure rules
     RId     : {τ₁ : cpstyp} {Δ : conttyp} →
               {e : cpsterm[ var , Δ ] τ₁} →
               cpsReduce e e
     RTrans  : {τ₁ : cpstyp} {Δ : conttyp} →
               {e₁ e₂ e₃ : cpsterm[ var , Δ ] τ₁} →
               cpsReduce e₁ e₂ →
               cpsReduce e₂ e₃ →
               cpsReduce e₁ e₃

  data cpsReduceV {var : cpstyp → Set} :
                  {τ₁ : cpstyp} →
                  cpsvalue[ var ] τ₁ →
                  cpsvalue[ var ] τ₁ → Set where
     -- λx.λk.V x k -> V
     REtaV   : {τ₀ τ₁ τ₃ τ₄ : cpstyp} →
               (v : cpsvalue[ var ] (τ₀ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)) →
               cpsReduceV (CPSFun (λ x → CPSApp v (CPSVar x) CPSKVar)) v
     -- congruence rule
     RFun    : {τ₀ τ₁ τ₃ τ₄ : cpstyp} →
               (e e' : var τ₀ → cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄) →
               ((x : var τ₀) → cpsReduce (e x) (e' x)) →
               cpsReduceV (CPSFun e) (CPSFun e')
     -- closure rules
     RId     : {τ₁ : cpstyp} →
               {v : cpsvalue[ var ] τ₁} →
               cpsReduceV v v
     RTrans  : {τ₁ : cpstyp} →
               {v₁ v₂ v₃ : cpsvalue[ var ] τ₁} →
               cpsReduceV v₁ v₂ →
               cpsReduceV v₂ v₃ →
               cpsReduceV v₁ v₃

  data cpsReduceC {var : cpstyp → Set} :
                  {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
                  cpscont[ var , Δ , τ₁ ] τ₂ →
                  cpscont[ var , Δ , τ₁ ] τ₂ → Set where
     -- (λx.K x) -> K
     REtaLet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               (k : cpscont[ var , Δ , τ₁ ] τ₂) →
               cpsReduceC (CPSKLet (λ x → CPSRet k (CPSVar x))) k

     -- congruence rule
     RKLet   : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {e e' : var τ₁ → cpsterm[ var , Δ ] τ₂} →
               ((x : var τ₁) → cpsReduce (e x) (e' x)) →
               cpsReduceC (CPSKLet e) (CPSKLet e')
     -- closure rules
     RId     : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {k : cpscont[ var , Δ , τ₁ ] τ₂} →
               cpsReduceC k k
     RTrans  : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {k₁ k₂ k₃ : cpscont[ var , Δ , τ₁ ] τ₂} →
               cpsReduceC k₁ k₂ →
               cpsReduceC k₂ k₃ →
               cpsReduceC k₁ k₃

-- equational reasoning
module Reasoning where

  open import Relation.Binary.PropositionalEquality

  infix  3 _∎
  infixr 2 _⟶⟨_⟩_ _≡⟨_⟩_
  infix  1 begin_

  begin_ : {var : cpstyp → Set} {τ₁ : cpstyp} {Δ : conttyp} →
           {e₁ e₂ : cpsterm[ var , Δ ] τ₁} →
           cpsReduce e₁ e₂ → cpsReduce e₁ e₂
  begin_ red = red

  _⟶⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} {Δ : conttyp} →
            (e₁ {e₂ e₃} : cpsterm[ var , Δ ] τ₁) →
            cpsReduce e₁ e₂ → cpsReduce e₂ e₃ → cpsReduce e₁ e₃
  _⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red-e₃ = RTrans e₁-red-e₂ e₂-red-e₃

  _≡⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} {Δ : conttyp} →
           (e₁ {e₂ e₃} : cpsterm[ var , Δ ] τ₁) →
           e₁ ≡ e₂ → cpsReduce e₂ e₃ →
           cpsReduce e₁ e₃
  _≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red-e₃ = e₂-red-e₃

  _∎ : {var : cpstyp → Set} {τ₁ : cpstyp} {Δ : conttyp} →
       (e : cpsterm[ var , Δ ] τ₁) → cpsReduce e e
  _∎ e = RId

-- lemma
mutual
  cpsSubstV≠ : {var : cpstyp → Set} {τ₁ τ : cpstyp} →
               (v₁ : cpsvalue[ var ] τ₁) →
               {v : cpsvalue[ var ] τ} →
               cpsSubstV (λ _ → v₁) v v₁
  cpsSubstV≠ (CPSVar x) = sVar≠
  cpsSubstV≠ (CPSNum n) = sNum
  cpsSubstV≠ (CPSFun e) = sFun (λ x → cpsSubst≠ (e x))
  cpsSubstV≠ CPSShift = sShift

  cpsSubst≠ : {var : cpstyp → Set} {τ₄ τ : cpstyp} {Δ : conttyp} →
              (e₁ : cpsterm[ var , Δ ] τ₄) →
              {v : cpsvalue[ var ] τ} →
              cpsSubst (λ _ → e₁) v e₁
  cpsSubst≠ (CPSRet k v) = sRet (cpsSubstC≠ k) (cpsSubstV≠ v)
  cpsSubst≠ (CPSApp v w k) = sApp (cpsSubstV≠ v) (cpsSubstV≠ w) (cpsSubstC≠ k)
  cpsSubst≠ (CPSShift2 e k) = sShift2 (λ k → cpsSubst≠ (e k)) (cpsSubstC≠ k)
  cpsSubst≠ (CPSRetE k e) = sRetE (cpsSubstC≠ k) (cpsSubst≠ e)

  cpsSubstC≠ : {var : cpstyp → Set} {τ₂ τ₄ τ : cpstyp} {Δ : conttyp} →
               (k₁ : cpscont[ var , Δ , τ₂ ] τ₄) →
               {v : cpsvalue[ var ] τ} →
               cpsSubstC (λ _ → k₁) v k₁
  cpsSubstC≠ CPSKVar = sKVar≠
  cpsSubstC≠ CPSKId = sKId
  cpsSubstC≠ (CPSKLet e) = sKLet λ x → cpsSubst≠ (e x)
