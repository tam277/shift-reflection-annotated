{-
  ============================================================================
  DS 項と DSKernel 項の間の Reflection (3)  (論文 4 節, 付録 B.3)
  ============================================================================
  DS 言語の簡約が、A-正規形変換した後の DSKernel 言語の簡約で保たれることを示す。
  論文の 定理 22 にあたる。
    correctVE : 任意の値 V, W について、V ⟶* W ならば V†† ⟶* W††
    correctE  : 任意の項 M, N と DSKernel 言語の継続 KΔ について、
                M ⟶* N ならば M :: KΔ ⟶* N :: KΔ
  そのために、次の補題を順に示している。
    lemma-substV, lemma-subst : 値の代入補題      (論文 補題 18)
    lemma-subst₂              : 継続の代入補題    (論文 補題 19)
    reduceK                   : 継続の簡約補題    (論文 補題 20)
    contExist                 : shift 用の補題    (論文 補題 21)
    reduceShift, reduceShift2 : (β.S) の場合の証明
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect3a where

open import DStermK
open import Embed
open import DSterm

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  値の代入補題 (論文 補題 18)
  ----------------------------------------------------------------------------
  代入してから A-正規形変換しても、A-正規形変換してから代入しても同じになる。
    lemma-substV : W[x:=V] = W′ ならば W††[x:=V††] = W′††
    lemma-subst  : M[x:=V] = M′ かつ KΔ[x:=V††] = KΔ′ ならば
                   (M :: KΔ)[x:=V††] = M′ :: KΔ′
  証明は代入関係 (SubstV, Subst) についての相互帰納法。
  いずれも代入関係として述べている（DSterm.agda の代入を参照）。
-}

mutual
  lemma-substV : {var : typK → Set} {τ τ₁ : typ} →
                 {v₁ : (var ∘ knormalT) τ → value[ var ∘ knormalT ] τ₁}
                 {v : value[ var ∘ knormalT ] τ}
                 {v₁′ : value[ var ∘ knormalT ] τ₁}
                 (sub : SubstV v₁ v v₁′) →
                 SubstVK {var} (λ m → knormalV (v₁ m)) (knormalV v)
                               (knormalV v₁′)
  lemma-substV sVar= = sVar=
  lemma-substV sVar≠ = sVar≠
  lemma-substV sNum = sNum
  lemma-substV (sFun sub) = sFun (λ x → lemma-subst (sub x) sKVar≠)
  lemma-substV sShift = sShift

  lemma-subst : {var : typK → Set} {τ τ₁ τ₂ τ₃ : typ} {Δ : conttypK} →
                {e : (var ∘ knormalT) τ →
                     term[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃}
                {k : (var ∘ knormalT) τ →
                     pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂}
                {v : value[ var ∘ knormalT ] τ}
                {e′ : term[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃}
                {k′ : pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂}
                (sub-e : Subst e v e′) →
                (sub-k : SubstCK k (knormalV v) k′) →
                SubstK (λ m → knormal (e m) (k m)) (knormalV v) (knormal e′ k′)
  lemma-subst (sVal sub-v) sub-k = sRet sub-k (lemma-substV sub-v)
  lemma-subst (sNonVal (sApp (sVal sub-v₁) (sVal sub-v₂))) sub-k =
    sApp (lemma-substV sub-v₁) (lemma-substV sub-v₂) sub-k
  lemma-subst (sNonVal (sApp (sVal sub-v₁) (sNonVal sub-e₂))) sub-k =
    lemma-subst (sNonVal sub-e₂) (sKLet (λ x →
      sApp (lemma-substV sub-v₁) sVar≠ sub-k))
  lemma-subst (sNonVal (sApp (sNonVal sub-e₁) (sVal sub-v₂))) sub-k =
    lemma-subst (sNonVal sub-e₁) (sKLet (λ x →
      sApp sVar≠ (lemma-substV sub-v₂) sub-k))
  lemma-subst (sNonVal (sApp (sNonVal sub-e₁) (sNonVal sub-e₂))) sub-k =
    lemma-subst (sNonVal sub-e₁) (sKLet (λ x →
      lemma-subst (sNonVal sub-e₂) (sKLet (λ y →
        sApp sVar≠ sVar≠ sub-k))))
  lemma-subst (sNonVal (sShift2 sub-e)) sub-k =
    sShift2 (λ x → lemma-subst (sub-e x) sKVar≠) sub-k
  lemma-subst (sNonVal (sReset sub-e)) sub-k =
    sRetE sub-k (lemma-subst sub-e sKId)
  lemma-subst (sNonVal (sLet sub-e₁ sub-e₂)) sub-k =
    lemma-subst sub-e₂ (sKLet (λ x → lemma-subst (sub-e₁ x) sub-k))

{-
  ----------------------------------------------------------------------------
  継続の代入補題 (論文 補題 19)
  ----------------------------------------------------------------------------
  継続 Kk の k に JΔ を代入してから M を変換しても、
  M を Kk の下で変換してから k に JΔ を代入しても同じになる。
    M :: (Kk[k:=JΔ]) = (M :: Kk)[k:=JΔ]
  証明は M についての帰納法。
-}

mutual
  lemma-subst₂ : {var : typK → Set}
                 {τ₁ τ₂ τ₃ : typ} {Δ : conttypK} {α β : typK} →
                 (e : term[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃)
                 {k : pcontextK[ var , K α ▷ β ,
                                 knormalT τ₁ ] knormalT τ₂}
                 {c : pcontextK[ var , Δ , α ] β}
                 {k′ : pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂}
                 (sub-k : SubstCK₂ k c k′) →
                 SubstK₂ (knormal e k) c (knormal e k′)
  lemma-subst₂ (Val v) sub-k = sRet sub-k
  lemma-subst₂ (NonVal (App (Val v₁) (Val v₂))) sub-k = sApp sub-k
  lemma-subst₂ (NonVal (App (Val v₁) (NonVal e₂))) sub-k =
    lemma-subst₂ (NonVal e₂) (sKLet (λ x → sApp sub-k))
  lemma-subst₂ (NonVal (App (NonVal e₁) (Val v₂))) sub-k =
    lemma-subst₂ (NonVal e₁) (sKLet (λ x → sApp sub-k))
  lemma-subst₂ (NonVal (App (NonVal e₁) (NonVal e₂))) sub-k =
    lemma-subst₂ (NonVal e₁) (sKLet (λ x →
      lemma-subst₂ (NonVal e₂) (sKLet (λ y →
        sApp sub-k))))
  lemma-subst₂ (NonVal (Shift2 e)) sub-k = sShift2 sub-k
  lemma-subst₂ (NonVal (Reset e)) sub-k = sRetE sub-k
  lemma-subst₂ (NonVal (Let e₁ e₂)) sub-k =
    lemma-subst₂ e₁ (sKLet (λ x → lemma-subst₂ (e₂ x) sub-k))

{-
  ----------------------------------------------------------------------------
  継続の簡約補題 (論文 補題 20)
  ----------------------------------------------------------------------------
  KΔ ⟶* KΔ′ ならば M :: KΔ ⟶* M :: KΔ′
  証明は M についての帰納法。
-}

reduceK : {var : typK → Set} {τ₁ τ₂ τ₃ : typ} {Δ : conttypK} →
          (e : term[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃) →
          {k k' : pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂} →
          ReduceCK k k' →
          ReduceK (knormal e k) (knormal e k')
reduceK (Val v) red = RRet₁ red
reduceK (NonVal (App (Val v₁) (Val v₂))) red = RApp₃ red
reduceK (NonVal (App (Val v₁) (NonVal e₂))) red =
  reduceK (NonVal e₂) (RKLet (λ x → RApp₃ red))
reduceK (NonVal (App (NonVal e₁) (Val v₂))) red =
  reduceK (NonVal e₁) (RKLet (λ x → RApp₃ red))
reduceK (NonVal (App (NonVal e₁) (NonVal e₂))) red =
  reduceK (NonVal e₁) (RKLet (λ x →
    reduceK (NonVal e₂) (RKLet (λ y → RApp₃ red))))
reduceK (NonVal (Shift2 e)) red = RShift₁ red
reduceK (NonVal (Reset e)) red = RRetE₁ red
reduceK (NonVal (Let e₁ e₂)) red =
  reduceK e₁ (RKLet (λ x → reduceK (e₂ x) red))

{-
  ----------------------------------------------------------------------------
  shift 用の補題 (論文 補題 21)
  ----------------------------------------------------------------------------
  DS 言語の pure なコンテキスト J と DSKernel 言語の継続 KΔ について、
  次の 2 つを満たす DSKernel 言語の継続 ĴΔ (j′) が存在する。
    ・任意の非値 P について        J[P] :: KΔ = P :: ĴΔ
    ・任意の値 V について          V :: ĴΔ ⟶* J[V] :: KΔ
  前半は、J を KΔ の方に押しやれることを表す。
  後半は、P を実行した結果の V でその後の実行を続けた結果と、
  元のコンテキスト J の下で実行を続けた結果が同じになることを表す。
  (β.S) の場合、つまり P が shift で J がその周りのコンテキストの場合に使う（論文 p.12）。
  証明は J についての帰納法で、Σ 型（存在）と × （かつ）で結果を返している。
-}

contExist : {var : typK → Set} {τ₁ τ₂ τ₆ : typ} {Δ : conttypK} →
            (j : pcontext[ var ∘ knormalT , τ₆ ▷ τ₆ , τ₁ ] τ₂)
            (k : pcontextK[ var , Δ , knormalT τ₆ ] knormalT τ₆) →
            Σ[ j′ ∈ pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂ ]
            ({τ₃ : typ} (p : nonvalue[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃) →
             knormal (plug j (NonVal p)) k ≡ knormal (NonVal p) j′) ×
            ((v : value[ var ∘ knormalT ] τ₁) →
             ReduceK (knormal {τ₂ = τ₂} (Val v) j′)
                     (knormal (plug j (Val v)) k))
contExist Hole k = (k , (λ p → refl) , λ _ → RId)
contExist (App₁ j (NonVal e)) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (App (NonVal p) (NonVal e))) ,
  λ v → begin
    Ret
     (KLet
      (λ m → knormal (NonVal e) (KLet (λ n → App (Var m) (Var n) j'))))
     (knormalV v)
  ⟶⟨ RBetaLet (lemma-subst (Subst≠ (NonVal e))
                            (sKLet (λ x → sApp sVar= sVar≠ (SubstKC≠ j')))) ⟩
    knormal (NonVal (App (Val v) (NonVal e))) j'
  ≡⟨ sym (eq (App (Val v) (NonVal e))) ⟩
    knormal (plug j (NonVal (App (Val v) (NonVal e)))) k
  ∎) where open DStermK.Reasoning
contExist (App₁ j (Val v)) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (App (NonVal p) (Val v))) ,
  λ v' → begin
    Ret (KLet (λ m → App (Var m) (knormalV v) j')) (knormalV v')
  ⟶⟨ RBetaLet (sApp sVar= (SubstKV≠ (knormalV v)) (SubstKC≠ j')) ⟩
    knormal (NonVal (App (Val v') (Val v))) j'
  ≡⟨ sym (eq (App (Val v') (Val v))) ⟩
    knormal (plug j (NonVal (App (Val v') (Val v)))) k
  ∎) where open DStermK.Reasoning
contExist (App₂ v j) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (App (Val v) (NonVal p))) ,
  λ v' → begin
    Ret (KLet (λ n → App (knormalV v) (Var n) j')) (knormalV v')
  ⟶⟨ RBetaLet (sApp (SubstKV≠ (knormalV v)) sVar= (SubstKC≠ j')) ⟩
    knormal (NonVal (App (Val v) (Val v'))) j'
  ≡⟨ sym (eq (App (Val v) (Val v'))) ⟩
    knormal (plug j (NonVal (App (Val v) (Val v')))) k
  ∎) where open DStermK.Reasoning
contExist (Let j e) k with contExist j k
... | j' , eq , red = (_ , (λ p → eq (Let (NonVal p) e)) ,
  λ v → begin
    Ret (KLet (λ m → knormal (e m) j')) (knormalV v)
  ≡⟨ sym (eq (Let (Val v) e)) ⟩
    knormal (plug j (NonVal (Let (Val v) e))) k
  ∎) where open DStermK.Reasoning

{-
  ----------------------------------------------------------------------------
  (β.S) の場合
  ----------------------------------------------------------------------------
  DS 言語の <J[S V]> ⟶ <V (λy.<J[y]>)> が、
  A-正規形変換した後でも DSKernel 言語の簡約で表せることを示す。
  contExist で得た Ĵ を使って、DSKernel 言語の (β.S) を適用し、
  その後、λ の中の Ĵ[y] を J[y] に戻している。
  reduceShift2 は、論文には無い Sk.M 版。
-}

reduceShift : {var : typK → Set} {τ₁ τ₃ τ₄ τ₅ τ₆ : typ}
              {τ₂  : typK} {Δ : conttypK}
              (k : pcontextK[ var , Δ , knormalT τ₁ ] τ₂)
              (v : value[ var ∘ knormalT ]
                   ((τ₃ ⇒ τ₄ cps[ τ₅ , τ₅ ]) ⇒ τ₆ cps[ τ₆ , τ₁ ]))
              (j : pcontext[ var ∘ knormalT , τ₆ ▷ τ₆ , τ₃ ] τ₄) →
              ReduceK
              (RetE k
               (knormal (plug j (NonVal (App (Val Shift) (Val v)))) KId))
              (RetE k
               (App (knormalV v)
                (Fun
                 (λ x → RetE KVar (knormal (plug j (Val (Var x))) KId)))
                KId))
reduceShift {var} k v j with contExist {var} j KId
... | j' , id , red = begin
    RetE k (knormal (plug j (NonVal (App (Val Shift) (Val v)))) KId)
  ≡⟨ cong (RetE k) (id (App (Val Shift) (Val v))) ⟩
    RetE k (knormal (NonVal (App (Val Shift) (Val v))) j')
  ⟶⟨ RShift ⟩
    RetE k
      (App (knormalV v) (Fun (λ y → RetE KVar (Ret j' (Var y)))) KId)
  ⟶⟨ RRetE₂ (RApp₂ (RFun _ _ (λ x → RRetE₂ (red (Var x))))) ⟩
    RetE k
      (App (knormalV v)
       (Fun (λ x → RetE KVar (knormal (plug j (Val (Var x))) KId))) KId)
  ∎ where open DStermK.Reasoning

reduceShift2 : {var : typK → Set} {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} {Δ : conttypK}
               (k : pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂)
               (v : (var ∘ knormalT) (τ₃ ⇒ τ₄ cps[ τ₅ , τ₅ ]) →
                    term[ var ∘ knormalT , τ₆ ▷ τ₆ ] τ₁)
               (j : pcontext[ var ∘ knormalT , τ₆ ▷ τ₆ , τ₃ ] τ₄) →
               ReduceK
               (RetE k (knormal (plug j (NonVal (Shift2 {τ₃ = τ₅} v))) KId))
               (RetE k
                (App (Fun (λ x → knormal (v x) KVar))
                 (Fun (λ x →
                  RetE KVar (knormal (plug j (Val (Var x))) KId))) KId))
reduceShift2 {var} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} k v j with contExist {var} j KId
... | j' , id , red = begin
    (RetE k (knormal (plug j (NonVal (Shift2 v))) KId))
  ≡⟨ cong (RetE k) (id (Shift2 v)) ⟩
    RetE k (knormal {τ₁ = τ₃} {τ₂ = τ₄} (NonVal (Shift2 {τ₃ = τ₅} v)) j')
  ⟶⟨ RShift2 ⟩
    RetE k
      (App (Fun (λ k₁ → knormal (v k₁) KVar))
       (Fun (λ y → RetE KVar (Ret j' (Var y)))) KId)
  ⟶⟨ RRetE₂ (RApp₂ (RFun _ _ (λ x → RRetE₂ (red (Var x))))) ⟩
    (RetE k
       (App (Fun (λ x → knormal (v x) KVar))
        (Fun (λ x → RetE KVar (knormal (plug j (Val (Var x))) KId))) KId))
  ∎ where open DStermK.Reasoning

{-
  ----------------------------------------------------------------------------
  主定理 (論文 定理 22)
  ----------------------------------------------------------------------------
  DS 言語の簡約規則 Reduce についての帰納法で証明する。
  (assoc), (let.1), (let.2) の場合は、A-正規形変換すると両辺が同じ項になるので RId で済む。
  A-正規形変換は、これらの規則で名前を付けた後の形を、最初から作っているからである。
  値から非値への簡約は reduceVal で起こりえないことを示し、() で場合を除いている。
-}

mutual
  correctVE : {var : typK → Set} {τ₁ β : typ}
              {v v' : value[ var ∘ knormalT ] τ₁}
              (red : Reduce {β = β} (Val v) (Val v')) →
              ReduceVK {var} (knormalV v) (knormalV v')
  correctVE (REtaV v) = REtaV (knormalV v)
  correctVE (RFun red) = RFun _ _ (λ x → correctE (red x))
  correctVE RId = RId
  correctVE (RTrans {e₂ = Val V} red₁ red₂) =
    RTrans (correctVE red₁) (correctVE red₂)
  correctVE (RTrans {e₂ = NonVal e₂} red₁ red₂) with reduceVal red₁
  ... | ()

  correctE : {var : typK → Set} {τ₁ τ₂ τ₃ : typ} {Δ : conttypK} →
             {e e′ : term[ var ∘ knormalT , τ₁ ▷ τ₂ ] τ₃} →
             {k : pcontextK[ var , Δ , knormalT τ₁ ] knormalT τ₂} →
             Reduce e e′ →
             ReduceK {var} (knormal e k) (knormal e′ k)
  correctE (RBetaV e₁ v₂ e₁′ sub) =
    RBetaV (lemma-subst sub sKVar≠) (lemma-subst₂ e₁′ sKVar=)
  correctE (REtaV v) = RRet₂ (REtaV (knormalV v))
  correctE (RBetaLet v₁ e₂ e₂′ sub) = RBetaLet (lemma-subst sub (SubstKC≠ _))
  correctE (REtaLet e₁) = reduceK e₁ (REtaLet _)
  correctE (RAssoc e₁ e₂ e₃) = RId
  correctE (RLet1 e₁ (Val v₂)) = RId
  correctE (RLet1 e₁ (NonVal e₂)) = RId
  correctE (RLet2 e₂) = RId
  correctE (RShift v j) = reduceShift _ v j
  correctE {τ₂ = τ₂} (RShift2 v j) = reduceShift2 {τ₂ = τ₂} _ v j
  correctE (RReset v₁) = RReset
  correctE (RFun red) = RRet₂ (RFun _ _ (λ x → correctE (red x)))
  correctE (RApp₁ {e₁ = Val v₁} {Val v₁′} {Val v₂} red) = RApp₁ (correctVE red)
  correctE (RApp₁ {e₁ = Val v₁} {Val v₁′} {NonVal e₂} red) =
    reduceK (NonVal e₂) (RKLet (λ x → RApp₁ (correctVE red)))
  correctE (RApp₁ {e₁ = Val v₁} {NonVal e₁′} {Val v₂} red) with reduceVal red
  ... | ()
  correctE (RApp₁ {e₁ = Val v₁} {NonVal e₁′} {NonVal e₂} red) with reduceVal red
  ... | ()
  correctE (RApp₁ {e₁ = NonVal e₁} {Val v₁′} {Val v₂} red) =
    RTrans (correctE red)
           (RBetaLet (sApp sVar= (SubstKV≠ (knormalV v₂)) (SubstKC≠ _)))
  correctE (RApp₁ {e₁ = NonVal e₁} {Val v₁′} {NonVal e₂} red) =
    RTrans (correctE red)
           (RBetaLet (lemma-subst (Subst≠ (NonVal e₂))
                       (sKLet (λ x → sApp sVar= sVar≠ (SubstKC≠ _)))))
  correctE (RApp₁ {e₁ = NonVal e₁} {NonVal e₁′} {Val v₂} red) = correctE red
  correctE (RApp₁ {e₁ = NonVal e₁} {NonVal e₁′} {NonVal e₂} red) = correctE red
  correctE (RApp₂ {e₂ = Val v₂} {Val v₂′} red) =
    RApp₂ (correctVE red)
  correctE (RApp₂ {e₂ = Val v₂} {NonVal e₂′} red) with reduceVal red
  ... | ()
  correctE (RApp₂ {e₂ = NonVal e₂} {Val v₂′} red) =
    RTrans (correctE red)
           (RBetaLet (sApp (SubstKV≠ (knormalV _)) sVar= (SubstKC≠ _)))
  correctE (RApp₂ {e₂ = NonVal e₂} {NonVal e₂′} red) = correctE red
  correctE (RLet₁ red) = correctE red
  correctE (RLet₂ {e₁ = e₁} red) =
    reduceK e₁ (RKLet (λ x → correctE (red x)))
  correctE (RShift₁ red) = RShift₂ (λ x → correctE (red x))
  correctE (RReset₁ red) = RRetE₂ (correctE red)
  correctE RId = RId
  correctE (RTrans red₁ red₂) = RTrans (correctE red₁) (correctE red₂)
