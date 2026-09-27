{-
  ============================================================================
  DS 項と DSKernel 項の間の Reflection (4)  (論文 4 節, 付録 B.4)
  ============================================================================
  DSKernel 言語の簡約が、DS 言語に埋め込んだ後の DS 言語の簡約で保たれることを示す。
  論文の 定理 27 にあたる。
    correctVE : 任意の値 V, W について       V ⟶* W ならば V⊙ ⟶* W⊙
    correctE  : 任意の項 MΔ, NΔ について   MΔ ⟶* NΔ ならば (MΔ)⊕ ⟶* (NΔ)⊕
    correctCE : 任意の継続 JΔ, KΔ について JΔ ⟶* KΔ ならば、
                任意の DS 言語の項 M について (JΔ)⊖[M] ⟶* (KΔ)⊖[M]
  そのために、次の仮定と補題を使っている。
    lemma-Var-SubstK                  : 変数を自分自身で置き換える仮定 (論文 仮定 23)
    lemma-SubstV, lemma-Subst,
    lemma-SubstC                      : 値の代入補題 (論文 補題 25)
    lemmaPlugSubst                    : 継続の代入についての補題 (論文 補題 26)
  （論文 補題 24 は、DSterm.agda の substPlug。）
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect4b where

open import DStermK
open import Embed
open import DSterm

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  仮定 (論文 仮定 5, 仮定 23)
  ----------------------------------------------------------------------------
  任意の DSKernel 言語の項 MΔ について MΔ[x:=x] = MΔ。
  MΔ の中の変数 x を x 自身で置き換えたら MΔ になる、という自明な命題だが、
  PHOAS では MΔ が λ 抽象の下に隠れていて場合分けできないため、証明できない。
  そのため postulate で仮定している（論文 p.13）。
  MΔ が具体的に与えられれば、Agda で示すことは簡単にできる。
  correctCE の (η.let) の場合で使う。
-}

postulate
  lemma-Var-SubstK : {var : typK → Set} {τ₃ τ₄ : typK} {Δ : conttypK}
                     {e : var τ₃ → termK[ var , Δ ] τ₄} →
                     {x : var τ₃} →
                     SubstK e (Var x) (e x)

{-
  ----------------------------------------------------------------------------
  値の代入補題 (論文 補題 25)
  ----------------------------------------------------------------------------
  代入してから埋め込んでも、埋め込んでから代入しても同じになる。
    lemma-SubstV : (W[x:=V])⊙ = W⊙[x:=V⊙]
    lemma-Subst  : (M[x:=V])⊕ = M⊕[x:=V⊙]
    lemma-SubstC : (KΔ[x:=V])⊖ = (KΔ)⊖[x:=V⊙]
  いずれも代入関係として述べていて、証明は代入関係についての相互帰納法。
  項の場合は、DSterm.agda の substPlug（論文 補題 24）を使う。
-}

mutual
  lemma-SubstV : {var : typ → Set} → {τ₁ τ₂ : typK} →
                 {v₁ : (var ∘ embedT) τ₁ →
                       valueK[ var ∘ embedT ] τ₂} →
                 {v : valueK[ var ∘ embedT ] τ₁} →
                 {v₂ : valueK[ var ∘ embedT ] τ₂} →
                 SubstVK v₁ v v₂ →
                 SubstV {var} (λ z → embedV (v₁ z)) (embedV v) (embedV v₂)
  lemma-SubstV sVar= = sVar=
  lemma-SubstV sVar≠ = sVar≠
  lemma-SubstV sNum = sNum
  lemma-SubstV (sFun sub) = sFun (λ x → lemma-Subst (sub x))
  lemma-SubstV sShift = sShift

  lemma-Subst : {var : typ → Set} {τ₁ τ₂ : typK} {Δ : conttypK} →
                {e : (var ∘ embedT) τ₂ → termK[ var ∘ embedT , Δ ] τ₁} →
                {v : valueK[ var ∘ embedT ] τ₂} →
                {e′ : termK[ var ∘ embedT , Δ ] τ₁} →
                SubstK e v e′ →
                Subst {var} (λ x → embed (e x)) (embedV v) (embed e′)
  lemma-Subst (sRet {k₁ = k₁}{k₂ = k₂} subCK subVK) =
    substPlug (lemma-SubstC subCK)
              (sVal (lemma-SubstV subVK))
  lemma-Subst (sApp subVK₁ subVK₂ subCK) =
    substPlug (lemma-SubstC subCK)
              (sNonVal (sApp (sVal (lemma-SubstV subVK₁))
                              (sVal (lemma-SubstV subVK₂))))
  lemma-Subst (sShift2 subK subCK) =
    substPlug (lemma-SubstC subCK)
              (sNonVal (sShift2 (λ x → lemma-Subst (subK x))))
  lemma-Subst (sRetE subCK subK) =
    substPlug (lemma-SubstC subCK)
              (sNonVal (sReset (lemma-Subst subK)))

  lemma-SubstC : {var : typ → Set} {τ₃ τ₄ τ₅ : typK}
                 {Δ : conttypK} →
                 {k₁ : (var ∘ embedT) τ₄ →
                       pcontextK[ var ∘ embedT , Δ , τ₃ ] τ₅} →
                 {v : valueK[ var ∘ embedT ] τ₄} →
                 {k₂ : pcontextK[ var ∘ embedT , Δ , τ₃ ] τ₅} →
                 SubstCK k₁ v k₂ →
                 SubstC {var} (λ x → embedC (k₁ x))
                              (embedV v)
                              (embedC k₂)
  lemma-SubstC sKVar≠ = sHole
  lemma-SubstC sKId = sHole
  lemma-SubstC {Δ = K τ₁ ▷ τ₂} (sKLet sub) =
    sLet sHole (λ x → lemma-Subst (sub x))
  lemma-SubstC {Δ = • τ} (sKLet sub) =
    sLet sHole (λ x → lemma-Subst (sub x))

{-
  ----------------------------------------------------------------------------
  継続の代入についての補題 (論文 補題 26)
  ----------------------------------------------------------------------------
  Mk[k:=c] = M′ ならば c⊖[(Mk)⊕] ⟶* M′⊕
  つまり、継続の代入をしてから埋め込んだものは、
  埋め込んだ Mk を、埋め込んだ c の穴に入れたものから簡約で得られる。
  c が []k, []•, let x = [] in N のどれかで、3 つの補題に分けている。
    lemmaReduceEmbedKVar : c = []k の場合
    lemmaReduceEmbedKId  : c = []• の場合
    lemmaReduceEmbedKLet : c = let x = [] in N の場合（(assoc) 規則を使う）
  lemmaPlugSubst は、これらを c で場合分けしてまとめたもの。
-}

-- following 3 lemma used in lemmaPlugSubst below
lemmaReduceEmbedKVar : {var : typ → Set} {τ₁ τ₂ τ₃ : typK}
                       {e e′ : termK[ var ∘ embedT , K τ₂ ▷ τ₃ ] τ₁}
                       (sub : SubstK₂ e KVar  e′) →
                       Reduce {var} (embed e) (embed e′)
lemmaReduceEmbedKVar (sRet sKVar=) = RId
lemmaReduceEmbedKVar (sRet (sKLet sub-e)) =
  RLet₂ (λ x → lemmaReduceEmbedKVar (sub-e x))
lemmaReduceEmbedKVar (sApp sKVar=) = RId
lemmaReduceEmbedKVar (sApp (sKLet sub-e)) =
  RLet₂ (λ x → lemmaReduceEmbedKVar (sub-e x))
lemmaReduceEmbedKVar (sShift2 sKVar=) = RId
lemmaReduceEmbedKVar (sShift2 (sKLet sub-e)) =
  RLet₂ (λ x → lemmaReduceEmbedKVar (sub-e x))
lemmaReduceEmbedKVar (sRetE sKVar=) = RId
lemmaReduceEmbedKVar (sRetE (sKLet sub-e)) =
  RLet₂ (λ x → lemmaReduceEmbedKVar (sub-e x))

lemmaReduceEmbedKId : {var : typ → Set} {τ₁ τ₂ : typK}
                      {e : termK[ var ∘ embedT , K τ₁ ▷ τ₁ ] τ₂}
                      {e′ : termK[ var ∘ embedT , • τ₁ ] τ₂}
                      (sub : SubstK₂ e KId e′) →
                      Reduce {var} (embed e) (embed e′)
lemmaReduceEmbedKId (sRet sKVar=) = RId
lemmaReduceEmbedKId (sRet (sKLet sub)) =
  RLet₂ (λ x → lemmaReduceEmbedKId (sub x))
lemmaReduceEmbedKId (sApp sKVar=) = RId
lemmaReduceEmbedKId (sApp (sKLet sub)) =
  RLet₂ (λ x → lemmaReduceEmbedKId (sub x))
lemmaReduceEmbedKId (sShift2 sKVar=) = RId
lemmaReduceEmbedKId (sShift2 (sKLet sub)) =
  RLet₂ (λ x → lemmaReduceEmbedKId (sub x))
lemmaReduceEmbedKId (sRetE sKVar=) = RId
lemmaReduceEmbedKId (sRetE (sKLet sub)) =
  RLet₂ (λ x → lemmaReduceEmbedKId (sub x))

lemmaReduceEmbedKLet : {var : typ → Set} {τ₁ τ₂ τ₃ α β : typK}
                       {Δ : conttypK}
                       {e : termK[ var ∘ embedT , K α ▷ β ] τ₁}
                       {e₂ : (var ∘ embedT) α →
                             termK[ var ∘ embedT , Δ ] β}
                       {e′ : termK[ var ∘ embedT , Δ ] τ₁}
                       (sub : SubstK₂ e (KLet e₂) e′) →
                       (delta : Δ-typeK Δ τ₂ τ₃) →
                       Reduce {var}
                              (NonVal (Let (embed e)
                                           (λ x → embed (e₂ x))))
                              (embed e′)
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sRet sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = • _} (sRet sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sRet (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = • _} (sRet (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sApp sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sApp (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = • _} (sApp sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = • _} (sApp (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sShift2 sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sShift2 (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = • _} (sShift2 sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = • _} (sShift2 (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sRetE sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = K _ ▷ _} (sRetE (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
lemmaReduceEmbedKLet {Δ = • _} (sRetE sKVar=) (refl , refl) = RId
lemmaReduceEmbedKLet {Δ = • _} (sRetE (sKLet sub-e)) (refl , refl) =
  RTrans (RAssoc _ _ _)
         (RLet₂ (λ x → lemmaReduceEmbedKLet (sub-e x) (refl , refl)))
{-
lemmaReduceEmbedKLet {e₂ = e₂}
  (sRetE {e = e} (sKLet {e₁ = e₁} {e₂ = e₂′} sub-e)) delta =
  begin
    NonVal
     (Let (NonVal (Let (NonVal (Reset (embed e (refl , refl))))
                       (λ x → embed (e₁ x) (refl , refl))))
      (λ x → embed (e₂ x) delta))
  ⟶⟨ RAssoc _ _ _ ⟩
    NonVal
      (Let (NonVal (Reset (embed e (refl , refl))))
       (λ x → NonVal (Let (embed (e₁ x) (refl , refl))
                          (λ x₁ → embed (e₂ x₁) delta))))
  ⟶⟨ RLet₂ _ _ _ (λ x → lemmaReduceEmbedKLet (sub-e x) delta) ⟩
    NonVal (Let (NonVal (Reset (embed e (refl , refl))))
                (λ x → embed (e₂′ x) delta))
  ∎ where open DSterm.Reasoning
-}

-- e[k:=c] = e′ => C[E] -> E′
lemmaPlugSubst : {var : typ → Set} {τ₁ α β : typK} {Δ₂ : conttypK}
                 {e  : termK[ var ∘ embedT , K α ▷ β ] τ₁}
                 {c  : pcontextK[ var ∘ embedT , Δ₂ , α ] β}
                 {e′ : termK[ var ∘ embedT , Δ₂ ] τ₁} →
                 (sub : SubstK₂ e c e′) →
                 Reduce {var} (plug (embedC c) (embed e)) (embed e′)
lemmaPlugSubst {c = KVar} sub = lemmaReduceEmbedKVar sub
lemmaPlugSubst {c = KId} sub = lemmaReduceEmbedKId sub
lemmaPlugSubst {Δ₂ = K x ▷ x₁} {c = KLet e₂} sub =
  lemmaReduceEmbedKLet sub (refl , refl)
lemmaPlugSubst {Δ₂ = • x} {c = KLet e₂} sub =
  lemmaReduceEmbedKLet sub (refl , refl)

{-
  ----------------------------------------------------------------------------
  主定理 (論文 定理 27)
  ----------------------------------------------------------------------------
  簡約 ReduceVK, ReduceK, ReduceCK についての相互帰納法。
  DSKernel 言語の各簡約規則を、対応する DS 言語の簡約規則に置き換える。
  埋め込んだ項は plug (embedC k) … の形をしているので、
  reducePlug で穴の中の簡約に持ち込むことが多い。
  (β.v) の場合は、値の代入補題と lemmaPlugSubst（継続の代入）を組み合わせる。
-}

mutual
  correctVE : {var : typ → Set} {τ₁ : typK} {β : typ}
              {v v' : valueK[ var ∘ embedT ] τ₁}
              (red : ReduceVK v v') →
              Reduce {var} {β = β} (Val (embedV v)) (Val (embedV v'))
  correctVE (REtaV v) = REtaV (embedV v)
  correctVE (RFun e e' red) = RFun (λ x → correctE (red x))
  correctVE RId = RId
  correctVE (RTrans red₁ red₂) = RTrans (correctVE red₁) (correctVE red₂)

  correctE : {var : typ → Set} {τ₃ : typK} {Δ : conttypK} →
             {e e′ : termK[ var ∘ embedT , Δ ] τ₃} →
             ReduceK e e′ →
             Reduce {var} (embed e) (embed e′)
  correctE {e′ = e′} (RBetaV {e₁ = e₁} {v} {c} {e₁′} sub sub2) = begin
      plug (embedC c)
       (NonVal (App (Val (Fun (λ x → embed (e₁ x)))) (Val (embedV v))))
    ⟶⟨ reducePlug (embedC c)
                   (RBetaV _ _ _ (lemma-Subst sub)) ⟩
      plug (embedC c) (embed e₁′)
    ⟶⟨ lemmaPlugSubst sub2 ⟩
      embed e′
    ∎ where open DSterm.Reasoning
  correctE {Δ = K τ₁ ▷ τ₂} {e′ = e′} (RBetaLet {e = e} {v} sub) =
    RBetaLet (embedV _) (λ x → embed (e x)) (embed e′) (lemma-Subst sub)
  correctE {Δ = • τ} {e′ = e′} (RBetaLet {e = e} {v} sub) =
    RBetaLet (embedV _) (λ x → embed (e x)) (embed e′) (lemma-Subst sub)
  correctE (RShift {j = j} {k}) =
    reducePlug (embedC k) (RShift _ (embedC j))
  correctE (RShift2 {j = j} {k}) =
    reducePlug (embedC k) (RShift2 _ (embedC j))
  correctE (RReset {v = v} {k}) =
    reducePlug (embedC k) (RReset (embedV v))
  correctE {τ₃ = τ₃} (RRet₁ red) = correctCE {τ₅ = τ₃} red
  correctE (RRet₂ {k = k} red) =
    reducePlug (embedC k) (correctVE red)
  correctE (RApp₁ {k = k} red) =
    reducePlug (embedC k) (RApp₁ (correctVE red))
  correctE (RApp₂ {k = k} red) =
    reducePlug (embedC k) (RApp₂ (correctVE red))
  correctE {τ₃ = τ₃} (RApp₃ red) = correctCE {τ₅ = τ₃} red
  correctE {τ₃ = τ₃} (RShift₁ red) = correctCE {τ₅ = τ₃} red
  correctE (RShift₂ {k = k} red) =
    reducePlug (embedC k) (RShift₁ (λ x → correctE (red x)))
  correctE {τ₃ = τ₃} (RRetE₁ red) = correctCE {τ₅ = τ₃} red
  correctE (RRetE₂ {k = k} {e} {e'} red) =
    reducePlug (embedC k) (RReset₁ (correctE red))
  correctE RId = RId
  correctE (RTrans red₁ red₂) = RTrans (correctE red₁) (correctE red₂)

  correctCE : {var : typ → Set} {τ₃ τ₄ τ₅ : typK} {Δ : conttypK}
              {k k' : pcontextK[ var ∘ embedT , Δ , τ₃ ] τ₄ }
              (redK : ReduceCK k k')
              {e : term[ var , embedT τ₃ ▷ embedT τ₄ ] embedT τ₅} →
              Reduce {var} (plug (embedC k) e)
                           (plug (embedC k') e)
  -- (η.let) の場合。
  -- K が let x = [] in N の場合は、(β.let) と仮定 lemma-Var-SubstK を使う。
  correctCE (REtaLet KVar) = REtaLet _
  correctCE (REtaLet KId) = REtaLet _
  correctCE {τ₃ = τ₃} {Δ = K τ₁ ▷ τ₂} (REtaLet (KLet e₂)) =
    RLet₂ (λ x → RBetaLet _ _ _
      (lemma-Subst {τ₂ = τ₃} {e = e₂} {e′ = e₂ x} lemma-Var-SubstK))
  correctCE {τ₃ = τ₃} {Δ = • τ} (REtaLet (KLet e₂)) =
    RLet₂ (λ x → RBetaLet _ _ _
      (lemma-Subst {τ₂ = τ₃} {e = e₂} {e′ = e₂ x} lemma-Var-SubstK))
  correctCE {Δ = K τ₁ ▷ τ₂} (RKLet red) = RLet₂ (λ x → correctE (red x))
  correctCE {Δ = • τ} (RKLet red) = RLet₂ (λ x → correctE (red x))
  correctCE RId = RId
  correctCE {τ₅ = τ₅} (RTrans redK₁ redK₂) =
    RTrans (correctCE {τ₅ = τ₅} redK₁) (correctCE {τ₅ = τ₅} redK₂)
