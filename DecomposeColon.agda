{-
  ============================================================================
  コロン変換の分解 (論文 1.1 節)
  ============================================================================
  コロン変換 (CPSColonTrans.agda の cpsE𝑐) が、
  A-正規形変換 (Embed.agda の knormal) と、
  DSKernel 言語用の CPS 変換 (DSTrans.agda の cpsE) の合成になることを証明する。
  つまり、従来の CPS 変換は
    DS 言語 --A-正規形変換--> DSKernel 言語 --CPS 変換--> CPS 言語
  と分解できる（論文 p.2 の図）。
  Reflect.agda の最後で import されている。
  （このファイルの REWRITE 規則が Reflect3.agda で解けない制約を生むため、
  最後に import する必要がある、と Reflect.agda に書かれている。）
  ============================================================================
-}

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

{-
  ----------------------------------------------------------------------------
  型の変換についての REWRITE 規則
  ----------------------------------------------------------------------------
  コロン変換の型の変換 CPSColonTrans.cpsT が、
  A-正規形変換の型の変換 knormalT と、DSTrans.cpsT の合成に等しいことを示し、
  REWRITE プラグマで、書き換え規則として登録している。
  （名前は cpsE∘knormalT だが、項ではなく型についての等式。）
-}

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

{-
  ----------------------------------------------------------------------------
  主定理
  ----------------------------------------------------------------------------
    correctV : 値 v について       v† = (v††)†′
                                   （cpsV𝑐 v ≡ cpsV (knormalV v)）
    correct  : 項 e と、DSKernel 言語のコンテキスト k について
                                   e : k‡ = (e :: k)°
                                   （cpsE𝑐 e (cpsC k) ≡ cpsE (knormal e k)）
  証明は v, e についての相互帰納法。
  コロン変換と A-正規形変換は同じ形の規則で定義されているので、
  各場合とも、帰納法の仮定を使って両辺をそろえるだけでよい。
  λ 抽象や let の本体では、関数の外延性の公理を使っている。

  App (NonVal e₁) (NonVal e₂) と Let (NonVal e₁) e₂ の場合は、
  Δ が K _ ▷ _ か • _ かで場合分けしているが、両者の証明は同じ。
  （Δ の形が決まらないと、計算が進まないため。）
-}

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

{-
  ----------------------------------------------------------------------------
  CPS 言語の継続を使った形
  ----------------------------------------------------------------------------
  CPS 言語の継続 k について、
    ((k♭)⊖[e] :: []k)° = e : k    （maincorrectC）
    ((k♭)⊖[e] :: []•)° = e : k    （maincorrectC2）
  が成り立つことを示す。
  つまり、DS 変換して埋め込んだコンテキストに e を plug し、A-正規形変換して CPS 変換したものは、
  e : k に等しい。
  Reflect2b.agda の correctC, correctC2 と、Reflect2a.agda の correctC を組み合わせている。
    maincorrectC  : k が k を使う継続 (Δ = K α ⇒ β) の場合
    maincorrectC2 : k が恒等継続の下の継続 (Δ = • γ) の場合
-}

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
