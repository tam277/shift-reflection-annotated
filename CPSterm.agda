{-
  ============================================================================
  CPS 言語 (論文 2.2 節)
  ============================================================================
  CPS 変換の変換先となる、継続渡し形式の言語（CPS 言語、論文では λcS*）を定義するファイル。
  以下を順に定義している。
    ・型と継続の型                       (論文 p.5, 図 3)
    ・項・値・継続                       (論文 p.5, 図 3。型規則は p.6, 図 4)
    ・インタプリタ
    ・代入関係（値の代入と、継続の代入）
    ・簡約規則                            (論文 p.5, 図 3)
    ・簡約の等式推論用の記法と補題
  DStermK.agda の DSKernel 言語とは、コンストラクタが一対一に対応している。
  （DSKernel 言語の説明も合わせて読むと分かりやすい。）
  ============================================================================
-}

module CPSterm where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  型の定義 (p.5, 図 3)
  ----------------------------------------------------------------------------
  論文の記法との対応:
    Nat                  : int
    τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄ : τ₂ → (τ₁ → τ₃) → τ₄
  関数は、τ₂ 型の引数と τ₁ → τ₃ 型の継続を受け取り、τ₄ 型の答えを返す。

  継続の型 conttyp は、論文の Δ と δ を合わせたものにあたる。
    K τ₁ ⇒ τ₂ : Δ = k の場合。継続の型は τ₁ →k τ₂。
    • τ       : Δ = • の場合。継続の型は τ →• τ（恒等継続 λx.x の型）。
  k は継続を表す特別な定数、• は恒等継続を表す（論文 p.5）。
-}

mutual
  data cpstyp : Set where
    Nat : cpstyp
    _⇒[_⇒_]⇒_ : cpstyp → cpstyp → cpstyp → cpstyp → cpstyp

  data conttyp : Set where
    K_⇒_ : cpstyp → cpstyp → conttyp
    •_ : cpstyp → conttyp

-- Δ-cpstype Δ τ₁ τ₂ : 継続の型 Δ が、τ₁ を受け取って τ₂ を返す継続の型であること。
-- （現在は他のファイルでは使われていない）
Δ-cpstype : conttyp → cpstyp → cpstyp → Set
Δ-cpstype (K τ₁′ ⇒ τ₂′) τ₁ τ₂ = τ₁′ ≡ τ₁ × τ₂′ ≡ τ₂
Δ-cpstype (• τ) τ₁ τ₂ = τ ≡ τ₁ × τ ≡ τ₂

{-
  ----------------------------------------------------------------------------
  項の定義 (p.5, 図 3。型規則は p.6, 図 4)
  ----------------------------------------------------------------------------
  論文の構文との対応:
    terms         MΔ   ::= KΔ V | V W KΔ | KΔ M•
    values        V, W  ::= x | λx.λk.Mk | S
    continuations KΔ   ::= k | λx.x | λx.MΔ
  すべての部分式に名前が付いている形で、V や W は値でなければならない（論文 p.5）。

  型との対応:
    cpsvalue[ var ] τ              : 値   (論文の Γ ⊢v V : τ)
    cpsterm[ var , Δ ] τ           : 項   (論文の Γ [Δ : δ] ⊢ MΔ : τ)
    cpscont[ var , Δ , τ₁ ] τ₂     : 継続 (論文の Γ [Δ : δ] ⊢k KΔ : τ₁ → τ₂)
  k は変数ではなく特別な定数として扱い、PHOAS の var には含めない。
  k の型は、型環境の代わりに Δ として引き回している（論文 p.6）。
-}

mutual
  data cpsvalue[_]_ (var : cpstyp → Set) : cpstyp → Set where
    -- x。(TVAR)
    CPSVar : {τ₁ : cpstyp} → (x : var τ₁) → cpsvalue[ var ] τ₁
    -- n
    CPSNum : (n : ℕ) → cpsvalue[ var ] Nat
    -- λx.λk.M。(TFUN)
    -- 継続 k は PHOAS の変数ではないので、Agda の関数が受け取るのは x だけ。
    -- 本体 Mk の型 cpsterm[ var , K τ₁ ⇒ τ₃ ] が、k の型 τ₁ →k τ₃ を保持している。
    CPSFun : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             (e : var τ₂ → cpsterm[ var , K τ₁ ⇒ τ₃ ] τ₄) →
             cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
    -- S。(TSHIFT)
    -- DS 言語の S を CPS 変換して得られる項
    --   S = λw.λj.w (λy.λk.k (j y)) (λx.x)
    -- を表す定数（論文 p.5）。
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             cpsvalue[ var ]
             (((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)
              ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)

  data cpsterm[_,_]_ (var : cpstyp → Set) : conttyp → cpstyp → Set where
    -- KΔ V。(TVAL)
    -- 値 V を継続 KΔ に渡す。
    CPSRet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
             (k : cpscont[ var , Δ , τ₁ ] τ₂) →
             (v : cpsvalue[ var ] τ₁) →
             cpsterm[ var , Δ ] τ₂
    -- V W KΔ。(TAPP)
    -- 関数 V を、引数 W と継続 KΔ で呼び出す。
    CPSApp : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → {Δ : conttyp} →
             (v : cpsvalue[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)) →
             (w : cpsvalue[ var ] τ₂) →
             (k : cpscont[ var , Δ , τ₁ ] τ₃) →
             cpsterm[ var , Δ ] τ₄
    -- (Sk.M) KΔ。
    -- DS 言語の special form の shift Sk.M を CPS 変換したもの（論文には無い）。
    -- 本体 M は、継続の型 τ₄ →k τ₄ の下で型が付く。
    CPSShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} → {Δ : conttyp} →
             (e : var (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) →
                  cpsterm[ var , K τ₄ ⇒ τ₄ ] τ₅) →
             (k : cpscont[ var , Δ , τ₁ ] τ₂) →
             cpsterm[ var , Δ ] τ₅
    -- KΔ M•。(TRESET)
    -- reset を CPS 変換した結果で、M• の結果を直接形式で継続 KΔ に渡している。
    -- ここで継続が区切られている（論文 p.5）。
    CPSRetE : {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
             (k : cpscont[ var , Δ , τ₁ ] τ₂) →
             (e : cpsterm[ var , • τ ] τ₁) →
             cpsterm[ var , Δ ] τ₂

  data cpscont[_,_,_]_ (var : cpstyp → Set) :
       conttyp → cpstyp → cpstyp → Set where
    -- 継続を表す定数 k。(TKVAR)
    CPSKVar : {τ₁ τ₂ : cpstyp} →
              cpscont[ var , K τ₁ ⇒ τ₂ , τ₁ ] τ₂
    -- 恒等継続 λx.x。(TKID)
    CPSKId  : {τ₁ : cpstyp} →
              cpscont[ var , • τ₁ , τ₁ ] τ₁
    -- 継続 λx.MΔ。(TKLET)
    CPSKLet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
              (e : var τ₁ → cpsterm[ var , Δ ] τ₂) →
              cpscont[ var , Δ , τ₁ ] τ₂

{-
  ----------------------------------------------------------------------------
  項の例
  ----------------------------------------------------------------------------
-}

-- λx.λk.k x
val1 : {var : cpstyp → Set} → {τ₁ τ₂ : cpstyp} →
       cpsvalue[ var ] (τ₁ ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₂)
val1 = CPSFun (λ x → CPSRet CPSKVar (CPSVar x))

{-
  ----------------------------------------------------------------------------
  インタプリタ
  ----------------------------------------------------------------------------
  DStermK.agda のインタプリタと同じ形をしている。
    〚 τ 〛   : 型 τ の意味
    〚 Δ 〛'  : 継続の型 Δ の意味（継続を表す Agda の関数の型）
    gv v      : 値 v の意味
    g e Δ     : 項 e を、継続 Δ の下で実行した結果
    gc k Δ    : 継続 k の意味
  g と gc の引数 Δ は、継続の型ではなく、k に与える継続そのもの（〚 Δ 〛' 型の値）である。
-}

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

{-
  ----------------------------------------------------------------------------
  値の代入 M[x:=V]
  ----------------------------------------------------------------------------
  DSterm.agda の代入と同じく、関係として定義している。
    cpsSubstV v₁ v v₂ : v₁[x:=v] = v₂（値への代入）
    cpsSubst  e₁ v e₂ : e₁[x:=v] = e₂（項への代入）
    cpsSubstC k₁ v k₂ : k₁[x:=v] = k₂（継続への代入）
  代入される側の v₁, e₁, k₁ は、
  「変数を受け取って項を返す Agda の関数」λ x → ... で表し、
  その x が代入される変数になる。
-}

mutual
  -- v₁[x:=v] = v₂
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

  -- e₁[x:=v] = e₂
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

  -- k₁[x:=v] = k₂
  data cpsSubstC {var : cpstyp → Set} :
                 {τ τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
                 (var τ → cpscont[ var , Δ , τ₁ ] τ₂) →
                 cpsvalue[ var ] τ →
                 cpscont[ var , Δ , τ₁ ] τ₂ → Set where
    -- k と λx.x には変数 x が現れないので、代入しても変わらない。
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

{-
  ----------------------------------------------------------------------------
  継続の代入 Mk[k:=KΔ]
  ----------------------------------------------------------------------------
    cpsSubst₂  e₁ c e₂ : e₁[k:=c] = e₂（項への代入）
    cpsSubstC₂ k₁ c k₂ : k₁[k:=c] = k₂（継続への代入）
  代入される側は、k を使う項（Δ = K α ⇒ β）でなければならない。
  値の中の k は、λx.λk. で束縛された別の k なので、
  値への代入は不要（論文 p.17 を参照）。
-}

mutual
  -- e₁[k:=c] = e₂
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

  -- k₁[k:=c] = k₂
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

{-
  ----------------------------------------------------------------------------
  簡約規則 (p.5, 図 3)
  ----------------------------------------------------------------------------
  項・値・継続それぞれについて簡約関係を定義し、相互再帰にしている。
    cpsReduce  e e′ : 項の簡約
    cpsReduceV v v′ : 値の簡約
    cpsReduceC k k′ : 継続の簡約
  DSterm.agda と同じく、1 ステップの簡約規則だけでなく、次の規則もまとめて定義している。
    ・合同規則 (congruence rules)    : 部分項が簡約できれば、それを含む項も簡約できる。
    ・反射律 RId (closure rules)     : 0 ステップの簡約。
    ・推移律 RTrans (closure rules)  : 簡約を 2 つつなげる。
  そのため、cpsReduce e e′ などは 0 ステップ以上の簡約 (⟶*) を表す。
  論文の規則と、定義されている場所の対応:
    (β.v), (β.let), (β.S), (β.R) : cpsReduce
    (η.v)                        : cpsReduceV
    (η.let)                      : cpsReduceC
  CPS 言語ではもともとすべての部分式に名前が付いているので、
  (let.1), (let.2), (assoc) に対応する規則は無い（論文 p.6）。
  DStermK.agda の ReduceK などと、規則が一対一に対応している。
-}

mutual
  data cpsReduce {var : cpstyp → Set} :
                 {τ₁ : cpstyp} → {Δ : conttyp} →
                 cpsterm[ var , Δ ] τ₁ →
                 cpsterm[ var , Δ ] τ₁ → Set where
     -- (β.v) (λx.λk.M) V K -> M[x:=V][k:=K]
     -- 値の代入 cpsSubst と、継続の代入 cpsSubst₂ を順に行う。
     -- 引数の代入と継続の代入が同時に行われる（論文 p.6）。
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
     -- (β.let) (λx.M) V -> M[x:=V]
     -- 継続 λx.M に値 V を渡したら、x に代入する。
     RBetaLet : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {e : var τ₁ → cpsterm[ var , Δ ] τ₂} →
               {v : cpsvalue[ var ] τ₁} →
               {e′ : cpsterm[ var , Δ ] τ₂} →
               cpsSubst e v e′ →
               cpsReduce (CPSRet (CPSKLet e) v) e′
     -- (β.S) K (S V J) -> K (V (λy.λk.k (J y)) (λx.x))
     -- j は恒等継続の下にある継続（Δ = • τ₄）。
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
     -- K ((Sk.M) J) -> K ((λk.M) (λy.λk.k (J y)) (λx.x))
     -- 論文には無い、CPSShift2 版の (β.S)。
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
     -- (β.R) K ((λx.x) V) -> K V
     -- reset の中身が (λx.x) V になったら reset を外す。
     RReset  : {τ₁ τ₂ : cpstyp} → {Δ : conttyp} →
               {v : cpsvalue[ var ] τ₁} →
               {k : cpscont[ var , Δ , τ₁ ] τ₂} →
               cpsReduce (CPSRetE k (CPSRet CPSKId v))
                         (CPSRet k v)

     -- congruence rules
     -- 部分項（値・継続・reset の中身・λ の本体など）が簡約できれば、
     -- それを含む項も簡約できる、という規則。
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
     -- (η.v) λx.λk.V x k -> V
     -- 受け取った値 x と継続 k を、そのまま V に渡すだけの関数は、V 自身に簡約できる。
     -- （論文の条件 x ∉ fv(V) は、V が λ x → の外側で与えられていて、
     -- V の中に x が現れようがないことで、自動的に満たされている。）
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
     -- (η.let) (λx.K x) -> K
     -- 受け取った値 x をそのまま K に渡すだけの継続は、K 自身に簡約できる。
     -- （論文の条件 x ∉ fv(K) は、K が λ x → の外側で与えられていて、
     -- K の中に x が現れようがないことで、自動的に満たされている。）
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

{-
  ----------------------------------------------------------------------------
  簡約の等式推論用の記法
  ----------------------------------------------------------------------------
  DSterm.agda の Reasoning と同じもの。
  他のファイルからは CPSterm.Reasoning として open して使う。
-}

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

{-
  ----------------------------------------------------------------------------
  代入に関する補題
  ----------------------------------------------------------------------------
  代入される変数が現れない場合、代入しても何も変わらない、という補題。
  つまり、x が現れない v₁, e₁, k₁ について、
  v₁[x:=v] = v₁、e₁[x:=v] = e₁、k₁[x:=v] = k₁ が成り立つ。
-}

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
