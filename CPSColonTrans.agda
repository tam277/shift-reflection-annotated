{-
  ============================================================================
  DS 言語から CPS 言語への CPS 変換（コロン変換）
  ============================================================================
  DS 言語の項を、直接 CPS 言語の項に変換する CPS 変換を定義するファイル。
  論文の M* にあたる、従来の CPS 変換である（論文 1.1 節）。
  論文には、この変換の定義は図としては載っていない。
  （p.2 に変換の例があり、p.10 でコロン変換 [12] に触れている。）
  コロン変換 (colon translation) [Plotkin 1975] の形で定義していて、
  cpsE𝑐 e k は e : k（項 e を、継続 k の下で CPS 変換する）を表す。

  この変換は、A-正規形変換 (Embed.agda の knormal) と、
  DSKernel 言語から CPS 言語への変換 (DSTrans.agda の cpsE) の合成に等しい。
  そのことは DecomposeColon.agda で証明している（論文 p.2）。
  変換規則の形は、Embed.agda の knormal とまったく同じになっている。
  ============================================================================
-}

module CPSColonTrans where

open import Data.Product
open import DSterm hiding (conttyp)
open import CPSterm
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  型の CPS 変換
  ----------------------------------------------------------------------------
  τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] を τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄ に変換する。
  （DSTrans.agda にも cpsT があるが、そちらは DSKernel 言語の型の変換。）
-}

cpsT : typ → cpstyp
cpsT Nat     = Nat
cpsT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  cpsT τ₂ ⇒[ cpsT τ₁ ⇒ cpsT τ₃ ]⇒ cpsT τ₄

{-
  ----------------------------------------------------------------------------
  項の CPS 変換（コロン変換）
  ----------------------------------------------------------------------------
    cpsV𝑐 v   : 値 v の CPS 変換
    cpsE𝑐 e k : 項 e を、CPS 言語の継続 k の下で CPS 変換した結果 (e : k)
  値でない部分式は、その結果を受け取る継続 λm.… を作って先に変換する。
  λ の本体は継続 k の下で、reset の中身は恒等継続 λx.x の下で変換する。
-}

mutual
  -- value
  cpsV𝑐 : {var : cpstyp → Set} → {τ₁ : typ} →
          value[ var ∘ cpsT ] τ₁ →
          cpsvalue[ var ] (cpsT τ₁)
  cpsV𝑐 (Var x) = CPSVar x
  cpsV𝑐 (Num n) = CPSNum n
  cpsV𝑐 (Fun e) = CPSFun (λ x → cpsE𝑐 (e x) CPSKVar)
  cpsV𝑐 Shift = CPSShift

  -- term
  cpsE𝑐 : {var : cpstyp → Set} →
          {τ₁ τ₂ τ₃ : typ} → {Δ : conttyp} →
          term[ var ∘ cpsT , τ₁ ▷ τ₂ ] τ₃ →
          cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂ →
          cpsterm[ var , Δ ] (cpsT τ₃)

  -- V : K = K V†
  cpsE𝑐 (Val v) k = CPSRet k (cpsV𝑐 v)

  -- P Q : K = P : (λm. Q : (λn. m n K))
  cpsE𝑐 (NonVal (App (NonVal e₁) (NonVal e₂))) k =
    cpsE𝑐 (NonVal e₁) (CPSKLet (λ m →
      cpsE𝑐 (NonVal e₂) (CPSKLet (λ n →
        CPSApp (CPSVar m) (CPSVar n) k))))

  -- P W : K = P : (λm. m W† K)
  cpsE𝑐 (NonVal (App (NonVal e₁) (Val v₂))) k =
    cpsE𝑐 (NonVal e₁) (CPSKLet (λ m →
      CPSApp (CPSVar m) (cpsV𝑐 v₂) k))

  -- V Q : K = Q : (λn. V† n K)
  cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂))) k =
    cpsE𝑐 (NonVal e₂) (CPSKLet (λ n →
      CPSApp (cpsV𝑐 v₁) (CPSVar n) k))

  -- V W : K = V† W† K
  cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k =
    CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k

  -- Sk.M : K
  -- 論文には無い。本体 M は継続 k の下で変換する。
  cpsE𝑐 (NonVal (Shift2 e)) k =
    CPSShift2 (λ k → cpsE𝑐 (e k) CPSKVar) k

  -- <M> : K = K (M : λx.x)
  cpsE𝑐 (NonVal (Reset e)) k =
    CPSRetE k (cpsE𝑐 e CPSKId)

  -- (let x = M in N) : K = M : (λm. N[x:=m] : K)
  cpsE𝑐 (NonVal (Let e₁ e₂)) k =
    cpsE𝑐 e₁ (CPSKLet (λ m →
      cpsE𝑐 (e₂ m) k))

{-
  ----------------------------------------------------------------------------
  CPS 変換の例
  ----------------------------------------------------------------------------
  DSterm.agda の例を変換したもの。
  各例の下のコメントは、変換結果の項。
-}

test1 : {var : cpstyp → Set} → {τ₁ τ₂ : typ} →
        cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test1 = cpsV𝑐 DSterm.val1
-- CPSFun (λ x → CPSRet CPSKVar (CPSVar x))

test2 : {var : cpstyp → Set} → {τ₁ τ₂ : typ} →
        cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test2 = cpsV𝑐 DSterm.val2
-- CPSFun (λ x →
--          CPSApp CPSShift
--                 (CPSFun (λ x₁ → CPSApp (CPSVar x₁) (CPSVar x) CPSKVar))
--                 CPSKVar)

test2' : {var : cpstyp → Set} → {τ₁ τ₂ : typ} →
         cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]))
test2' = cpsV𝑐 DSterm.val2'
-- CPSFun (λ x →
--   CPSShift2 (λ k → CPSApp (CPSVar k) (CPSVar x) CPSKVar) CPSKVar)

test3 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ τ : typ} →
        cpsvalue[ var ] (cpsT (τ₁ ⇒ τ₂ cps[ τ₃ , τ₁ ]))
test3 {τ = τ} = cpsV𝑐 (DSterm.val3 {τ = τ})
-- λ {τ} →
--   CPSFun (λ x →
--     CPSApp CPSShift
--            (CPSFun (λ x₁ → CPSRet CPSKVar (CPSVar x)))
--            CPSKVar)

-- test4 = cpsV𝑐 DSterm.val4
-- test4' = cpsV𝑐 DSterm.val4'
{-
CPSFun (λ x → CPSRet CPSKVar
  (CPSFun (λ y → CPSRet CPSKVar
    (CPSFun (λ z → CPSRet CPSKVar
      (CPSFun (λ w →
        CPSApp (CPSVar x) (CPSVar y)
               (CPSKLet (λ m →
                 CPSApp (CPSVar z) (CPSVar w)
                        (CPSKLet (λ n →
                          CPSApp (CPSVar m) (CPSVar n) CPSKVar)))))))))))
-}

-- test5 = cpsV𝑐 DSterm.val5

{-
  ----------------------------------------------------------------------------
  補題
  ----------------------------------------------------------------------------
-}

-- e : (λn.v n k) ⟶* (v e) : k
-- e が値のときは (β.let) で 1 ステップ簡約する。
-- e が非値のときは、コロン変換の定義から両辺が同じ項になる。
-- （現在は他のファイルでは使われていない。）
colon₂ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {Δ : conttyp} →
         (v₁ : value[ var ∘ cpsT ] (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ])) →
         (e₂ : term[ var ∘ cpsT , τ₄ ▷ τ₅ ] τ₃) →
         (k : cpscont[ var , Δ , cpsT τ₁ ] cpsT τ₂) →
         cpsReduce (cpsE𝑐 e₂ (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
                   (cpsE𝑐 (NonVal (App (Val v₁) e₂)) k)
colon₂ v₁ (Val v₂) k = begin
    (cpsE𝑐 (Val v₂) (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)))
  ≡⟨ refl ⟩
    (CPSRet (CPSKLet (λ n → CPSApp (cpsV𝑐 v₁) (CPSVar n) k)) (cpsV𝑐 v₂))
  ⟶⟨ RBetaLet (sApp (cpsSubstV≠ (cpsV𝑐 v₁)) sVar= (cpsSubstC≠ k)) ⟩
    (CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k)
  ≡⟨ refl ⟩
    (cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k)
  ∎ where open CPSterm.Reasoning
colon₂ v₁ (NonVal e₂) k = RId
