{-# OPTIONS --rewriting #-}

module Reflect3 where

open import DSterm hiding (conttyp)
open import CPSterm
open import CPSColonTrans

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- substitution lemma
mutual
  lemma-substV : {var : cpstyp → Set} {τ τ₁ : typ} →
                 {v₁ : (var ∘ cpsT) τ → value[ var ∘ cpsT ] τ₁}
                 {v : value[ var ∘ cpsT ] τ}
                 {v₁′ : value[ var ∘ cpsT ] τ₁}
                 (sub : SubstV v₁ v v₁′) →
                 cpsSubstV {var} (λ m → cpsV𝑐 (v₁ m)) (cpsV𝑐 v) (cpsV𝑐 v₁′)
  lemma-substV sVar= = sVar=
  lemma-substV sVar≠ = sVar≠
  lemma-substV sNum = sNum
  lemma-substV (sFun sub) = sFun (λ x → lemma-subst _ _ (sub x) sKVar≠)
  lemma-substV sShift = sShift

  lemma-subst : {var : cpstyp → Set} {τ τ₁ τ₂ τ₃ : typ} {Δ : conttyp} →
                {e : (var ∘ cpsT) τ → term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃}
                (k : (var ∘ cpsT) τ → cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂)
                {v : value[ var ∘ cpsT ] τ}
                {e′ : term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃}
                (k′ : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂)
                (sub-e : Subst e v e′) →
                (sub-k : cpsSubstC k (cpsV𝑐 v) k′) →
                cpsSubst (λ m → cpsE𝑐 (e m) (k m)) (cpsV𝑐 v) (cpsE𝑐 e′ k′)
  lemma-subst k k′ (sVal sub-e) sub-k = sRet sub-k (lemma-substV sub-e)
  lemma-subst k k′ (sNonVal (sApp (sVal sub-e₁) (sVal sub-e₂))) sub-k =
    sApp (lemma-substV sub-e₁) (lemma-substV sub-e₂) sub-k
  lemma-subst k k′ (sNonVal (sApp (sVal {v₁ = v₁} {v₁′ = v₁′} sub-e₁)
                                  (sNonVal sub-e₂))) sub-k =
    lemma-subst
      (λ m → CPSKLet (λ n → CPSApp (cpsV𝑐 (v₁ m)) (CPSVar n) (k m)))
      (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁′) (CPSVar n) k′))
      (sNonVal sub-e₂)
      (sKLet (λ x → sApp (lemma-substV sub-e₁) (cpsSubstV≠ (CPSVar x)) sub-k))
  lemma-subst k k′ (sNonVal (sApp (sNonVal sub-e₁)
                                  (sVal {v₁ = v₁} {v₁′ = v₁′} sub-e₂))) sub-k =
    lemma-subst
      (λ m → CPSKLet (λ m₁ → CPSApp (CPSVar m₁) (cpsV𝑐 (v₁ m)) (k m)))
      (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v₁′) k′))
      (sNonVal sub-e₁)
      (sKLet (λ x → sApp (cpsSubstV≠ (CPSVar x)) (lemma-substV sub-e₂) sub-k))
  lemma-subst k k′ (sNonVal (sApp (sNonVal sub-e₁)
                                  (sNonVal {e = e} {e′ = e′} sub-e₂))) sub-k =
    lemma-subst
      (λ m → CPSKLet (λ m₁ →
        cpsE𝑐 (NonVal (e m))
              (CPSKLet (λ n → CPSApp (CPSVar m₁) (CPSVar n) (k m)))))
      (CPSKLet (λ m →
        cpsE𝑐 (NonVal e′)
              (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k′))))
      (sNonVal sub-e₁)
      (sKLet (λ x → lemma-subst
        (λ y → CPSKLet (λ n → CPSApp (CPSVar x) (CPSVar n) (k y)))
        (CPSKLet (λ n → CPSApp (CPSVar x) (CPSVar n) k′))
        (sNonVal sub-e₂)
        (sKLet (λ x₁ →
          sApp (cpsSubstV≠ (CPSVar x)) (cpsSubstV≠ (CPSVar x₁)) sub-k))))
  lemma-subst k k′ (sNonVal (sShift2 sub-e)) sub-k =
    sShift2 (λ x → lemma-subst (λ x₁ → CPSKVar) CPSKVar (sub-e x) sKVar≠) sub-k
  lemma-subst k k′ (sNonVal (sReset sub-e)) sub-k =
    sRetE sub-k (lemma-subst (λ _ → CPSKId) CPSKId sub-e sKId)
  lemma-subst k k′ (sNonVal (sLet {e₂ = e₂} {e₂′ = e₂′} sub-e₁ sub-e₂)) sub-k =
    lemma-subst (λ m → CPSKLet (λ m₁ → cpsE𝑐 (e₂ m m₁) (k m)))
                (CPSKLet (λ m → cpsE𝑐 (e₂′ m) k′)) sub-e₂
                (sKLet (λ x → lemma-subst k k′ (sub-e₁ x) sub-k))

mutual
  lemma-subst₂ : {var : cpstyp → Set}
                 {τ₁ τ₂ τ₃ α β : typ} {Δ : conttyp} →
                 {e : term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃}
                 (k : cpscont[ var , K cpsT α ⇒ cpsT β , cpsT τ₁ ] cpsT τ₂)
                 {c : cpscont[ var , Δ , cpsT α ] cpsT β}
                 (k′ : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂)
                 (sub-k : cpsSubstC₂ k c k′) →
                 cpsSubst₂ (cpsE𝑐 e k) c (cpsE𝑐 e k′)
  lemma-subst₂ {e = Val v} k k′ sub-k = sRet sub-k
  lemma-subst₂ {e = NonVal (App (NonVal e₁) (NonVal e₂))} k k′ sub-k =
    lemma-subst₂ {e = NonVal e₁} _ _ (sKLet (λ x →
      lemma-subst₂ {e = NonVal e₂} _ _ (sKLet (λ y →
        sApp sub-k))))
  lemma-subst₂ {e = NonVal (App (NonVal e₁) (Val v₂))} k k′ sub-k =
    lemma-subst₂ {e = NonVal e₁} _ _ (sKLet (λ x →
      sApp sub-k))
  lemma-subst₂ {e = NonVal (App (Val v₁) (NonVal e₂))} k k′ sub-k =
    lemma-subst₂ {e = NonVal e₂} _ _ (sKLet (λ x →
      sApp sub-k))
  lemma-subst₂ {e = NonVal (App (Val v₁) (Val v₂))} k k′ sub-k =
    sApp sub-k
  lemma-subst₂ {e = NonVal (Shift2 e)} k k′ sub-k = sShift2 sub-k
  lemma-subst₂ {e = NonVal (Reset e)} k k′ sub-k = sRetE sub-k
  lemma-subst₂ {e = NonVal (Let e₁ e₂)} k k′ sub-k =
    lemma-subst₂ {e = e₁} _ _ (sKLet (λ x → lemma-subst₂ {e = e₂ x} _ _ sub-k))

-- lemma
reduceK : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} {Δ : conttyp} →
          (e : term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃) →
          (k k' : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂) →
          cpsReduceC k k' →
          cpsReduce (cpsE𝑐 e k) (cpsE𝑐 e k')
reduceK (Val v) k k' red = begin
    (cpsE𝑐 (Val v) k)
  ≡⟨ refl ⟩
    (CPSRet k (cpsV𝑐 v))
  ⟶⟨ RRet₁ red ⟩
    (CPSRet k' (cpsV𝑐 v))
  ≡⟨ refl ⟩
    (cpsE𝑐 (Val v) k')
  ∎ where open CPSterm.Reasoning
reduceK (NonVal (App (Val v₁) (Val v₂))) k k' red = RApp₃ red
reduceK (NonVal (App (Val v₁) (NonVal e₂))) k k' red =
  reduceK (NonVal e₂)
          (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k))
          (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k'))
          (RKLet (λ x → RApp₃ red))
reduceK (NonVal (App (NonVal e₁) (Val v₂))) k k' red =
  reduceK (NonVal e₁)
          (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v₂) k))
          (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v₂) k'))
          (RKLet (λ x → RApp₃ red))
reduceK (NonVal (App (NonVal e₁) (NonVal e₂))) k k' red =
  reduceK (NonVal e₁)
          (CPSKLet
            (λ m →
               cpsE𝑐 (NonVal e₂)
                     (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k))))
          (CPSKLet
            (λ m →
               cpsE𝑐 (NonVal e₂)
                     (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k'))))
          (RKLet (λ x →
            reduceK (NonVal e₂)
                    (CPSKLet (λ n → CPSApp (CPSVar x) (CPSVar n) k))
                    (CPSKLet (λ n → CPSApp (CPSVar x) (CPSVar n) k'))
                    (RKLet (λ x₁ → RApp₃ red))))
reduceK (NonVal (Shift2 e)) k k' red = RShift₁ red
reduceK (NonVal (Reset e)) k k' red = begin
    (cpsE𝑐 (NonVal (Reset e)) k)
  ≡⟨ refl ⟩
    (CPSRetE k (cpsE𝑐 e CPSKId))
  ⟶⟨ RRetE₁ red ⟩
    (CPSRetE k' (cpsE𝑐 e CPSKId))
  ≡⟨ refl ⟩
    (cpsE𝑐 (NonVal (Reset e)) k')
  ∎ where open CPSterm.Reasoning
reduceK (NonVal (Let e₁ e₂)) k k' red = begin
    (cpsE𝑐 (NonVal (Let e₁ e₂)) k)
  ≡⟨ refl ⟩
    (cpsE𝑐 e₁ (CPSKLet (λ m → cpsE𝑐 (e₂ m) k)))
  ⟶⟨ reduceK e₁ (CPSKLet (λ z → cpsE𝑐 (e₂ z) k))
                  (CPSKLet (λ z → cpsE𝑐 (e₂ z) k'))
                  (RKLet (λ x → reduceK (e₂ x) k k' red)) ⟩
    (cpsE𝑐 e₁ (CPSKLet (λ m → cpsE𝑐 (e₂ m) k')))
  ≡⟨ refl ⟩
    (cpsE𝑐 (NonVal (Let e₁ e₂)) k')
  ∎ where open CPSterm.Reasoning

contExist : {var : cpstyp → Set} {τ₁ τ₂ τ₆ : typ} {Δ : conttyp} →
            (j : pcontext[ var ∘ cpsT , τ₆ ▷ τ₆ , τ₁ ] τ₂)
            (k : cpscont[ var , Δ , cpsT τ₆ ] cpsT τ₆) →
            Σ[ j′ ∈ cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂ ]
            ({τ₃ : typ} (p : nonvalue[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃) →
             cpsE𝑐 (plug j (NonVal p)) k ≡ cpsE𝑐 (NonVal p) j′) ×
            ((v : value[ var ∘ cpsT ] τ₁) →
             cpsReduce (cpsE𝑐 (Val v) j′) (cpsE𝑐 (plug j (Val v)) k))
contExist Hole k = (k , (λ p → refl) , λ _ → RId)
contExist (App₁ j (NonVal e)) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (App (NonVal p) (NonVal e))) ,
  λ v → begin
    CPSRet (CPSKLet (λ m →
             cpsE𝑐 (NonVal e)
               (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) j'))))
           (cpsV𝑐 v)
  ⟶⟨ RBetaLet (lemma-subst {e = λ _ → NonVal e}
                 (λ m → CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) j'))
                 (CPSKLet (λ z → CPSApp (cpsV𝑐 v) (CPSVar z) j'))
                 (Subst≠ (NonVal e))
                 (sKLet (λ x → sApp sVar= sVar≠ (cpsSubstC≠ j')))) ⟩
    cpsE𝑐 (NonVal e) (CPSKLet (λ z → CPSApp (cpsV𝑐 v) (CPSVar z) j'))
  ≡⟨ refl ⟩
    cpsE𝑐 (NonVal (App (Val v) (NonVal e))) j'
  ≡⟨ sym (eq (App (Val v) (NonVal e))) ⟩
    cpsE𝑐 (plug j (NonVal (App (Val v) (NonVal e)))) k
  ∎) where open CPSterm.Reasoning
contExist (App₁ j (Val v)) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (App (NonVal p) (Val v))) ,
  λ v' → begin
    CPSRet (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v) j')) (cpsV𝑐 v')
  ⟶⟨ RBetaLet (sApp sVar= (cpsSubstV≠ (cpsV𝑐 v)) (cpsSubstC≠ j')) ⟩
    CPSApp (cpsV𝑐 v') (cpsV𝑐 v) j'
  ≡⟨ refl ⟩
    cpsE𝑐 (NonVal (App (Val v') (Val v))) j'
  ≡⟨ sym (eq (App (Val v') (Val v))) ⟩
    cpsE𝑐 (plug j (NonVal (App (Val v') (Val v)))) k
  ∎) where open CPSterm.Reasoning
contExist (App₂ v j) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (App (Val v) (NonVal p))) ,
  λ v' → begin
    CPSRet (CPSKLet (λ n → CPSApp (cpsV𝑐 v) (CPSVar n) j')) (cpsV𝑐 v')
  ⟶⟨ RBetaLet (sApp (cpsSubstV≠ (cpsV𝑐 v)) sVar= (cpsSubstC≠ j')) ⟩
    CPSApp (cpsV𝑐 v) (cpsV𝑐 v') j'
  ≡⟨ refl ⟩
    cpsE𝑐 (NonVal (App (Val v) (Val v'))) j'
  ≡⟨ sym (eq (App (Val v) (Val v'))) ⟩
    cpsE𝑐 (plug j (NonVal (App (Val v) (Val v')))) k
  ∎) where open CPSterm.Reasoning
contExist (Let j e) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (Let (NonVal p) e)) ,
  λ v → begin
    CPSRet (CPSKLet (λ m → cpsE𝑐 (e m) j')) (cpsV𝑐 v)
  ≡⟨ refl ⟩
    cpsE𝑐 (NonVal (Let (Val v) e)) j'
  ≡⟨ sym (eq (Let (Val v) e)) ⟩
    cpsE𝑐 (plug j (NonVal (Let (Val v) e))) k
  ∎) where open CPSterm.Reasoning

reduceShift : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} {Δ : conttyp}
              (k : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂)
              (v : value[ var ∘ cpsT ]
                   ((τ₃ ⇒ τ₄ cps[ τ₅ , τ₅ ]) ⇒ τ₆ cps[ τ₆ , τ₁ ]))
              (j : pcontext[ var ∘ cpsT , τ₆ ▷ τ₆ , τ₃ ] τ₄) →
              cpsReduce
              (CPSRetE k
               (cpsE𝑐 (plug j (NonVal (App (Val Shift) (Val v)))) CPSKId))
              (CPSRetE k
               (CPSApp (cpsV𝑐 v)
                (CPSFun
                 (λ x → CPSRetE CPSKVar (cpsE𝑐 (plug j (Val (Var x))) CPSKId)))
                CPSKId))
reduceShift {var} k v j
  with contExist {var} j CPSKId
... | j' , id , red = begin
    CPSRetE k
      (cpsE𝑐 (plug j (NonVal (App (Val Shift) (Val v)))) CPSKId)
  ≡⟨ cong (CPSRetE k) (id (App (Val Shift) (Val v))) ⟩
    CPSRetE k (cpsE𝑐 (NonVal (App (Val Shift) (Val v))) j')
  ⟶⟨ RShift ⟩
    CPSRetE k
      (CPSApp (cpsV𝑐 v)
       (CPSFun (λ y → CPSRetE CPSKVar (CPSRet j' (CPSVar y)))) CPSKId)
  ⟶⟨ RRetE₂ (RApp₂ (RFun _ _ (λ x → RRetE₂ (red (Var x))))) ⟩
    CPSRetE k
      (CPSApp (cpsV𝑐 v)
       (CPSFun
        (λ x → CPSRetE CPSKVar (cpsE𝑐 (plug j (Val (Var x))) CPSKId)))
       CPSKId)
  ∎ where open CPSterm.Reasoning

reduceShift2 : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} {Δ : conttyp}
               (k : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂)
               (v : (var ∘ cpsT) (τ₃ ⇒ τ₄ cps[ τ₅ , τ₅ ]) →
                    term[ var ∘ cpsT , τ₆ ▷ τ₆ ] τ₁)
               (j : pcontext[ var ∘ cpsT , τ₆ ▷ τ₆ , τ₃ ] τ₄) →
               cpsReduce
               (CPSRetE k (cpsE𝑐 (plug j (NonVal (Shift2 v))) CPSKId))
               (CPSRetE k
                (CPSApp (CPSFun (λ x → cpsE𝑐 (v x) CPSKVar))
                 (CPSFun (λ x →
                  CPSRetE CPSKVar (cpsE𝑐 (plug j (Val (Var x))) CPSKId)))
                 CPSKId))
reduceShift2 {var} k v j
  with contExist {var} j CPSKId
... | j' , id , red = begin
    CPSRetE k (cpsE𝑐 (plug j (NonVal (Shift2 v))) CPSKId)
  ≡⟨ cong (CPSRetE k) (id (Shift2 v)) ⟩
    CPSRetE k (cpsE𝑐 (NonVal (Shift2 v)) j')
  ⟶⟨ RShift2 ⟩
    CPSRetE k
      (CPSApp (CPSFun (λ k₁ → cpsE𝑐 (v k₁) CPSKVar))
       (CPSFun (λ y → CPSRetE CPSKVar (CPSRet j' (CPSVar y)))) CPSKId)
  ⟶⟨ RRetE₂ (RApp₂ (RFun _ _ λ x → RRetE₂ (red (Var x)))) ⟩
    CPSRetE k
       (CPSApp (CPSFun (λ x → cpsE𝑐 (v x) CPSKVar))
        (CPSFun
         (λ x → CPSRetE CPSKVar (cpsE𝑐 (plug j (Val (Var x))) CPSKId)))
        CPSKId)
  ∎ where open CPSterm.Reasoning

-- main theorem
mutual
  correctV : {var : cpstyp → Set} → {τ₁ β : typ} →
             {v v′ : value[ var ∘ cpsT ] τ₁} →
             Reduce {β = β} (Val v) (Val v′) →
             cpsReduceV {var} (cpsV𝑐 v) (cpsV𝑐 v′)
  correctV (REtaV v) = REtaV (cpsV𝑐 v)
  correctV (RFun {e = e} {e′} red) =
    RFun (λ x → cpsE𝑐 (e x) CPSKVar) (λ x → cpsE𝑐 (e′ x) CPSKVar)
         (λ x → correct _ (red x))
  correctV RId = RId
  correctV (RTrans {e₂ = Val v₂} red₁ red₂) =
    RTrans (correctV red₁) (correctV red₂)
  correctV (RTrans {e₂ = NonVal e₂} red₁ red₂) with reduceVal red₁
  ... | ()

  correct : {var : cpstyp → Set} →
            {τ₁ τ₂ τ₃ : typ} → {Δ : conttyp} →
            {e e′ : term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃} →
            (k : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂) →
            Reduce e e′ →
            cpsReduce (cpsE𝑐 e k)
                      (cpsE𝑐 e′ k)
  correct k (RBetaV e₁ v₂ e₁′ sub) = begin
      (cpsE𝑐 (NonVal (App (Val (Fun e₁)) (Val v₂))) k)
    ≡⟨ refl ⟩
      (CPSApp (CPSFun (λ x → cpsE𝑐 (e₁ x) CPSKVar)) (cpsV𝑐 v₂) k)
    -- ⟶⟨ RBetaV (lemma-subst₂ _ _ sub sKVar=) ⟩
    ⟶⟨ RBetaV (lemma-subst _ _ sub sKVar≠)
               (lemma-subst₂ {e = e₁′} _ _ sKVar=) ⟩
      (cpsE𝑐 e₁′ k)
    ∎ where open CPSterm.Reasoning
  correct k (REtaV v) = begin
      (cpsE𝑐 (Val (Fun (λ x → NonVal (App (Val v) (Val (Var x)))))) k)
    ≡⟨ refl ⟩
      (CPSRet k (CPSFun (λ x → CPSApp (cpsV𝑐 v) (CPSVar x) CPSKVar)))
    ⟶⟨ RRet₂ (REtaV (cpsV𝑐 v)) ⟩
      (CPSRet k (cpsV𝑐 v))
    ≡⟨ refl ⟩
      (cpsE𝑐 (Val v) k)
    ∎ where open CPSterm.Reasoning
  correct k (RBetaLet v₁ e₂ e₂′ sub) = begin
      (cpsE𝑐 (NonVal (Let (Val v₁) e₂)) k)
    ≡⟨ refl ⟩
      (CPSRet (CPSKLet (λ m → cpsE𝑐 (e₂ m) k)) (cpsV𝑐 v₁))
    ⟶⟨ RBetaLet (lemma-subst _ _ sub (cpsSubstC≠ k)) ⟩
      (cpsE𝑐 e₂′ k)
    ∎ where open CPSterm.Reasoning
  correct k (REtaLet e₁) = begin
      (cpsE𝑐 (NonVal (Let e₁ (λ x → Val (Var x)))) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 e₁ (CPSKLet (λ m → CPSRet k (CPSVar m))))
    ⟶⟨ reduceK e₁ (CPSKLet (λ m → CPSRet k (CPSVar m))) k (REtaLet k) ⟩
      (cpsE𝑐 e₁ k)
    ∎ where open CPSterm.Reasoning
  correct k (RAssoc e₁ e₂ e₃) = RId
  correct k (RLet1 e₁ (Val v₂)) = RId
  correct k (RLet1 e₁ (NonVal e₂)) = RId
  correct k (RLet2 e₂) = RId
  correct k (RShift v j) = begin
      (cpsE𝑐 (NonVal (Reset (plug j (NonVal (App (Val Shift) (Val v)))))) k)
    ≡⟨ refl ⟩
      (CPSRetE k
       (cpsE𝑐 (plug j (NonVal (App (Val Shift) (Val v)))) CPSKId))
    ⟶⟨ reduceShift k v j  ⟩
      (CPSRetE k
       (CPSApp (cpsV𝑐 v)
        (CPSFun
         (λ x →
            CPSRetE CPSKVar (cpsE𝑐 (plug j (Val (Var x))) CPSKId)))
        CPSKId))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (Reset (NonVal (App (Val v)
               (Val (Fun (λ y → NonVal (Reset (plug j (Val (Var y)))))))))))
             k)
    ∎ where open CPSterm.Reasoning
  correct k (RShift2 v j) = reduceShift2 k v j
  correct k (RReset v₁) = begin
      (cpsE𝑐 (NonVal (Reset (Val v₁))) k)
    ≡⟨ refl ⟩
      (CPSRetE k (CPSRet CPSKId (cpsV𝑐 v₁)))
    ⟶⟨ RReset ⟩
      (CPSRet k (cpsV𝑐 v₁))
    ≡⟨ refl ⟩
      (cpsE𝑐 (Val v₁) k)
    ∎ where open CPSterm.Reasoning
  correct k (RFun {e = e} {e′} red) = begin
      (cpsE𝑐 (Val (Fun e)) k)
    ≡⟨ refl ⟩
      (CPSRet k (CPSFun (λ x → cpsE𝑐 (e x) CPSKVar)))
    ⟶⟨ RRet₂ (RFun (λ x → cpsE𝑐 (e x) CPSKVar)
                    (λ x → cpsE𝑐 (e′ x) CPSKVar)
                    (λ x → correct CPSKVar (red x))) ⟩
      (CPSRet k (CPSFun (λ x → cpsE𝑐 (e′ x) CPSKVar)))
    ≡⟨ refl ⟩
      (cpsE𝑐 (Val (Fun e′)) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₁ {e₁ = Val v₁} {Val v₁′} {Val v₂} red) = begin
      (cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k)
    ≡⟨ refl ⟩
      (CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k)
    ⟶⟨ RApp₁ (correctV red) ⟩
      (CPSApp (cpsV𝑐 v₁′) (cpsV𝑐 v₂) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁′) (Val v₂))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₁ {e₁ = Val v₁} {Val v₁′} {NonVal e₂} red) = begin
      (cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂))) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal e₂) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
    ⟶⟨ reduceK (NonVal e₂) _ _ (RKLet (λ x → RApp₁ (correctV red))) ⟩
      (cpsE𝑐 (NonVal e₂) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁′) (CPSVar n) k)))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁′) (NonVal e₂))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₁ {e₁ = Val v₁} {NonVal e₁′} {Val x} red) with reduceVal red
  ... | ()
  correct k (RApp₁ {e₁ = Val v₁} {NonVal e₁′} {NonVal x} red) with reduceVal red
  ... | ()
  correct k (RApp₁ {e₁ = NonVal e₁} {Val v₁′} {Val v₂} red) = begin
      (cpsE𝑐 (NonVal (App (NonVal e₁) (Val v₂))) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal e₁) (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v₂) k)))
    ⟶⟨ correct _ red ⟩
      cpsE𝑐 (Val v₁′) (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v₂) k))
    ≡⟨ refl ⟩
      (CPSRet (CPSKLet (λ m → CPSApp (CPSVar m) (cpsV𝑐 v₂) k))
       (cpsV𝑐 v₁′))
    ⟶⟨ RBetaLet (sApp sVar= (cpsSubstV≠ (cpsV𝑐 v₂)) (cpsSubstC≠ k)) ⟩
      (CPSApp (cpsV𝑐 v₁′) (cpsV𝑐 v₂) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁′) (Val v₂))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₁ {e₁ = NonVal e₁} {Val v₁′} {NonVal e₂} red) = begin
      (cpsE𝑐 (NonVal (App (NonVal e₁) (NonVal e₂))) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal e₁)
       (CPSKLet
        (λ m →
           cpsE𝑐 (NonVal e₂)
           (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k)))))
    ⟶⟨ correct _ red ⟩
      (cpsE𝑐 (Val v₁′)
       (CPSKLet
        (λ m →
           cpsE𝑐 (NonVal e₂)
           (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k)))))
    ≡⟨ refl ⟩
      (CPSRet
       (CPSKLet
        (λ m →
           cpsE𝑐 (NonVal e₂) (CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k))))
       (cpsV𝑐 v₁′))
    ⟶⟨ RBetaLet (lemma-subst
          (λ m → CPSKLet (λ n → CPSApp (CPSVar m) (CPSVar n) k))
          (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁′) (CPSVar n) k))
          (Subst≠ (NonVal e₂))
          (sKLet (λ x → sApp sVar= (cpsSubstV≠ (CPSVar x)) (cpsSubstC≠ k)))) ⟩
      (cpsE𝑐 (NonVal e₂)
       (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁′) (CPSVar n) k)))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁′) (NonVal e₂))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₁ {e₁ = NonVal e₁} {NonVal e₁′} {Val v₂} red) = correct _ red
  correct k (RApp₁ {e₁ = NonVal e₁} {NonVal e₁′} {NonVal e₂} red) =
    correct _ red
  correct k (RApp₂ {v₁ = v₁} {Val v₂} {Val v₂′} red) = begin
      (cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k)
    ≡⟨ refl ⟩
      (CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k)
    ⟶⟨ RApp₂ (correctV red) ⟩
      (CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂′) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁) (Val v₂′))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₂ {v₁ = v₁} {Val v₂} {NonVal e₂′} red) with reduceVal red
  ... | ()
  correct k (RApp₂ {v₁ = v₁} {NonVal e₂} {Val v₂′} red) = begin
      (cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂))) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal e₂) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
    ⟶⟨ correct _ red ⟩
      cpsE𝑐 (Val v₂′) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k))
    ≡⟨ refl ⟩
      CPSRet (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)) (cpsV𝑐 v₂′)
    ⟶⟨ RBetaLet (sApp (cpsSubstV≠ (cpsV𝑐 v₁)) sVar= (cpsSubstC≠ k)) ⟩
      (CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂′) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁) (Val v₂′))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RApp₂ {v₁ = v₁} {NonVal e₂} {NonVal e₂′} red) = begin
      (cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂))) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal e₂) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
    ⟶⟨ correct _ red ⟩
      (cpsE𝑐 (NonVal e₂′)
       (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂′))) k)
    ∎ where open CPSterm.Reasoning
  correct k (RLet₁ {e₁ = e₁} {e₁′} {e₂} red) = begin
      (cpsE𝑐 (NonVal (Let e₁ e₂)) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 e₁ (CPSKLet (λ m → cpsE𝑐 (e₂ m) k)))
    ⟶⟨ correct (CPSKLet (λ m → cpsE𝑐 (e₂ m) k)) red ⟩
      (cpsE𝑐 e₁′ (CPSKLet (λ m → cpsE𝑐 (e₂ m) k)))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (Let e₁′ e₂)) k)
    ∎ where open CPSterm.Reasoning
  correct k (RLet₂ {e₁ = e₁} {e₂} {e₂′} red) = begin
      (cpsE𝑐 (NonVal (Let e₁ e₂)) k)
    ≡⟨ refl ⟩
      (cpsE𝑐 e₁ (CPSKLet (λ m → cpsE𝑐 (e₂ m) k)))
    ⟶⟨ reduceK e₁
                (CPSKLet (λ m → cpsE𝑐 (e₂ m) k))
                (CPSKLet (λ m → cpsE𝑐 (e₂′ m) k))
                (RKLet (λ y → correct k (red y))) ⟩
      (cpsE𝑐 e₁ (CPSKLet (λ m → cpsE𝑐 (e₂′ m) k)))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (Let e₁ e₂′)) k)
    ∎ where open CPSterm.Reasoning
  correct k (RShift₁ red) = RShift₂ (λ x → correct CPSKVar (red x))
  correct k (RReset₁ {e = e} {e′} red) = begin
      (cpsE𝑐 (NonVal (Reset e)) k)
    ≡⟨ refl ⟩
      (CPSRetE k (cpsE𝑐 e CPSKId))
    ⟶⟨ RRetE₂ (correct CPSKId red) ⟩
      (CPSRetE k (cpsE𝑐 e′ CPSKId))
    ≡⟨ refl ⟩
      (cpsE𝑐 (NonVal (Reset e′)) k)
    ∎ where open CPSterm.Reasoning
  correct k RId = RId
  correct k (RTrans {e₁ = e₁} {e₂} {e₃} e₁-red-e₂ e₂-red-e₃) = begin
      (cpsE𝑐 e₁ k)
    ⟶⟨ correct k e₁-red-e₂ ⟩
      (cpsE𝑐 e₂ k)
    ⟶⟨ correct k e₂-red-e₃ ⟩
      (cpsE𝑐 e₃ k)
    ∎ where open CPSterm.Reasoning

-- main theorem using Reflect3a, Reflect3b

open import Reflect3a
open import Reflect3b
open import DSTrans
open import Embed

correctV' : {var : cpstyp → Set} → {τ₁ β : typ} →
            {v v′ : value[ var ∘ DSTrans.cpsT ∘ knormalT ] τ₁} →
            Reduce {β = β} (Val v) (Val v′) →
            cpsReduceV {var} (cpsV (knormalV v)) (cpsV (knormalV v′))
correctV' red = correctVK (correctVE red)

correct' : {var : cpstyp → Set} →
           {τ₁ τ₂ τ₃ : typ} → {Δ : conttyp} →
           {e e′ : term[ var ∘ DSTrans.cpsT ∘ knormalT , τ₁ ▷ τ₂ ] τ₃} →
           (k : cpscont[ var , Δ , DSTrans.cpsT (knormalT τ₁) ]
                       DSTrans.cpsT (knormalT τ₂)) →
           Reduce e e′ →
           cpsReduce (cpsE (knormal e (dsC k)))
                     (cpsE (knormal e′ (dsC k)))
correct' k red = correctK (correctE red)
