{-
  ============================================================================
  DSKernel 言語 (論文 2.3 節)
  ============================================================================
  shift/reset 入りのカーネル言語（DSKernel 言語、論文では λcS▷）を定義するファイル。
  DSKernel 言語は、DS 言語を A-正規形に変換したときに得られる項の言語で、
  見た目は直接形式だが、CPS 言語と一対一に対応している（論文 p.7）。
  以下を順に定義している。
    ・型と継続の型                       (論文 p.8, 図 5)
    ・項・値・コンテキスト               (論文 p.8, 図 5。型規則は p.8, 図 6)
    ・インタプリタ
    ・代入関係（値の代入と、継続の代入）
    ・簡約規則                            (論文 p.8, 図 5)
    ・簡約の等式推論用の記法と補題
  CPSterm.agda の CPS 言語とは、コンストラクタが一対一に対応している。
  ============================================================================
-}

module DStermK where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

{-
  ----------------------------------------------------------------------------
  型の定義 (p.8, 図 5)
  ----------------------------------------------------------------------------
  型 typK は、DS 言語の型 typ と同じ形をしている。
    Nat                    : int
    τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] : τ₂ → τ₁@[τ₃, τ₄]

  継続の型 conttypK は、論文の Δ と δ を合わせたものにあたる。
    K τ₁ ▷ τ₂ : Δ = k の場合。継続の型は τ₁ →k τ₂。
    • τ       : Δ = • の場合。継続の型は τ →• τ（恒等継続なので、入力と出力の型が同じ）。
  k か • かは、その項が CPS 変換される前に、
  reset で囲まれていなかったか（k）、囲まれていたか（•）を表す（論文 p.5）。
  DS 言語の conttyp と違って、この区別が型の情報として必要になる（論文 2.2 節）。
-}

data typK : Set where
  Nat          : typK
  _⇒_cps[_,_]  : typK → typK → typK → typK → typK

data conttypK : Set where
  K_▷_ : typK → typK → conttypK
  •_ : typK → conttypK

-- Δ-typeK Δ τ₁ τ₂ : 継続の型 Δ が、τ₁ を受け取って τ₂ を返す継続の型であること。
-- • τ の場合は、τ₁ と τ₂ がどちらも τ に等しいことになる。
-- （Reflect4b.agda で使われている。）
Δ-typeK : conttypK → typK → typK → Set
Δ-typeK (K τ₁′ ▷ τ₂′) τ₁ τ₂ = τ₁′ ≡ τ₁ × τ₂′ ≡ τ₂
Δ-typeK (• τ) τ₁ τ₂ = τ ≡ τ₁ × τ ≡ τ₂

{-
  ----------------------------------------------------------------------------
  項の定義 (p.8, 図 5。型規則は p.8, 図 6)
  ----------------------------------------------------------------------------
  論文の構文との対応:
    terms    MΔ   ::= KΔ[V] | KΔ[V W] | KΔ[<M•>]
    values   V, W  ::= x | λx.Mk | S
    contexts KΔ   ::= []k | []• | let x = [] in MΔ
  項 MΔ は、どれも「コンテキスト KΔ の穴に何かが入った形」をしている。
  DS 言語と違って、値でない部分式には必ず let で名前が付いている（A-正規形）。

  型との対応:
    valueK[ var ] τ                : 値     (論文の Γ ⊢v V : τ)
    termK[ var , Δ ] τ             : 項     (論文の Γ [Δ : δ] ⊢ MΔ : τ)
    pcontextK[ var , Δ , τ₁ ] τ₂   : コンテキスト (論文の Γ [Δ : δ] ⊢k KΔ : τ₁ → τ₂)
  Δ は、項の中で最後に使われる継続（[]k か []•）の型を表す。
-}

mutual
  data valueK[_]_ (var : typK → Set) : typK → Set where
    -- x。(TVAR)
    Var   : {τ₁ : typK} → var τ₁ → valueK[ var ] τ₁
    -- n
    Num   : ℕ → valueK[ var ] Nat
    -- λx.M。(TFUN)
    -- 本体 Mk は [k : τ₁ →k τ₃] の下で型が付く。
    -- 項としては k は現れないが、本体の型 termK[ var , K τ₁ ▷ τ₃ ] で k の型を保持している。
    Fun   : {τ₀ τ₁ τ₃ τ₄ : typK} →
            (var τ₀ → termK[ var , K τ₁ ▷ τ₃ ] τ₄) →
            valueK[ var ] (τ₀ ⇒ τ₁ cps[ τ₃ , τ₄ ])
    -- S。(TSHIFT)
    -- 型は DS 言語の Shift と同じ。
    Shift : {τ₁ τ₂ τ₃ τ₄ τ₅ : typK} →
            valueK[ var ]
            (((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])
             ⇒ τ₁ cps[ τ₂ , τ₅ ])

  data termK[_,_]_ (var : typK → Set) : conttypK → typK → Set where
    -- 以下の項はすべて、最後に使う継続の型 Δ を持つ。
    -- KΔ[V]。(TVAL)
    -- 値 V をコンテキスト KΔ の穴に入れる。CPS 言語の KΔ V に対応する。
    Ret  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
           pcontextK[ var , Δ , τ₁ ] τ₂ →
           valueK[ var ] τ₁ →
           termK[ var , Δ ] τ₂
    -- KΔ[V W]。(TAPP)
    -- 関数適用の結果をコンテキスト KΔ に渡す。CPS 言語の V W KΔ に対応する。
    App  : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
           valueK[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) →
           valueK[ var ] τ₂ →
           pcontextK[ var , Δ , τ₁ ] τ₃ →
           termK[ var , Δ ] τ₄
    -- KΔ[Sk.M]。論文には無い、special form の shift（DSterm.agda の Shift2 に対応）。
    -- 本体 M は [k : τ₄ →k τ₄] の下で型が付く。
    Shift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ : typK} → {Δ : conttypK} →
           (var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → termK[ var , K τ₄ ▷ τ₄ ] τ₅) →
           pcontextK[ var , Δ , τ₁ ] τ₂ →
           termK[ var , Δ ] τ₅
    -- KΔ[<M•>]。(TRESET)
    -- reset の中身 M• は、最後の継続が []• であるような項（Δ = • τ）。
    -- M• の結果をコンテキスト KΔ に渡す。CPS 言語の KΔ M• に対応する。
    RetE : {τ τ₁ τ₂ : typK} → {Δ : conttypK} →
           pcontextK[ var , Δ , τ₁ ] τ₂ →
           termK[ var , • τ ] τ₁ →
           termK[ var , Δ ] τ₂

  data pcontextK[_,_,_]_ (var : typK → Set) : conttypK → typK → typK → Set where
    -- []k。(TKVAR)
    -- 穴だけのコンテキストで、CPS 言語の継続変数 k に対応する。
    KVar  : {τ₁ τ₂ : typK} →
            pcontextK[ var , K τ₁ ▷ τ₂ , τ₁ ] τ₂
    -- []•。(TKID)
    -- 穴だけのコンテキストで、CPS 言語の恒等継続 λx.x に対応する。
    -- 恒等継続なので、入力と出力の型が同じ τ₁ になる。
    KId   : {τ₁ : typK} →
            pcontextK[ var , • τ₁ , τ₁ ] τ₁
    -- let x = [] in MΔ。(TKLET)
    -- CPS 言語の継続 λx.MΔ に対応する。
    KLet  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
            (e₂ : var τ₁ → termK[ var , Δ ] τ₂) →
            pcontextK[ var , Δ , τ₁ ] τ₂

{-
  ----------------------------------------------------------------------------
  項の例
  ----------------------------------------------------------------------------
-}

-- λx.λk.k x
val1 : {var : typK → Set} → {τ₁ τ₂ : typK} →
       valueK[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val1 = Fun (λ x → Ret KVar (Var x))

{-
  ----------------------------------------------------------------------------
  インタプリタ
  ----------------------------------------------------------------------------
  DSterm.agda のインタプリタと同様に、意味を CPS で与える。
    〚 τ 〛   : 型 τ の意味
    〚 Δ 〛'  : 継続の型 Δ の意味（継続を表す Agda の関数の型）
    gv v      : 値 v の意味
    g e Δ     : 項 e を、継続 Δ の下で実行した結果
    gc k Δ    : コンテキスト k の意味（継続 Δ の下での、継続としての意味）
  g と gc の引数 Δ は、継続の型ではなく、継続そのもの（〚 Δ 〛' 型の値）である。
-}

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
  -- DSterm.agda の gp (Shift2 e) k と同じ動き。
  -- 捕まえる継続は、コンテキスト k の意味 gc k Δ になる。
  g (Shift2 e k) Δ = g (e (λ x₂ k₂ → k₂ (gc k Δ x₂))) (λ x → x)
  -- reset の中身 e を恒等継続の下で実行し、その結果を k に渡す。
  g (RetE k e) Δ = (gc k Δ) (g e (λ x → x))

  gc : {τ₁ τ₂ : typK} {Δ : conttypK} →
       pcontextK[ 〚_〛 , Δ , τ₁ ] τ₂ → 〚 Δ 〛'  → 〚 τ₁ 〛 → 〚 τ₂ 〛
  -- []k は、外から与えられた継続そのもの。
  -- []• は恒等継続。
  -- let x = [] in M は、受け取った値を x に束縛して M を実行する継続。
  gc KVar k = k
  gc KId Δ = λ x → x
  gc (KLet e) Δ = λ x → g (e x) Δ

{-
  ----------------------------------------------------------------------------
  値の代入 M[x:=V]
  ----------------------------------------------------------------------------
  DSterm.agda の代入と同じく、関係として定義している。
    SubstVK v₁ v v₂ : v₁[x:=v] = v₂（値への代入）
    SubstK  e₁ v e₂ : e₁[x:=v] = e₂（項への代入）
    SubstCK k₁ v k₂ : k₁[x:=v] = k₂（コンテキストへの代入）
  代入される側の v₁, e₁, k₁ は、
  「変数を受け取って項を返す Agda の関数」λ x → ... で表し、
  その x が代入される変数になる。
-}

mutual
  -- v₁[x:=v] = v₂
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

  -- e₁[x:=v] = e₂
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

  -- k₁[x:=v] = k₂
  data SubstCK {var : typK → Set} : {τ α β : typK} → {Δ : conttypK} →
               (var τ → pcontextK[ var , Δ , α ] β) →
               valueK[ var ] τ →
               pcontextK[ var , Δ , α ] β → Set where
    -- []k と []• には変数 x が現れないので、代入しても変わらない。
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

{-
  ----------------------------------------------------------------------------
  継続の代入 Mk[k:=KΔ]
  ----------------------------------------------------------------------------
  DSKernel 言語では k は項に現れないので、
  「[]k（KVar）をコンテキスト c で置き換える」ことで継続の代入を表す。
    SubstK₂  e₁ c e₂ : e₁[k:=c] = e₂（項への代入）
    SubstCK₂ k₁ c k₂ : k₁[k:=c] = k₂（コンテキストへの代入）
  代入される側は、最後の継続が []k の項（Δ = K α ▷ β）でなければならない。
  CPS 言語と同じく、値には k が現れない（λ の中の k は別の k を指す）ため、
  値への代入は不要（論文 p.17 を参照）。
-}

mutual
  -- e₁[k:=c] = e₂
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

  -- k₁[k:=c] = k₂
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

{-
  ----------------------------------------------------------------------------
  簡約規則 (p.8, 図 5)
  ----------------------------------------------------------------------------
  項・値・コンテキストそれぞれについて簡約関係を定義し、相互再帰にしている。
    ReduceK  e e′ : 項の簡約
    ReduceVK v v′ : 値の簡約
    ReduceCK k k′ : コンテキストの簡約
  DSterm.agda と同じく、1 ステップの簡約規則だけでなく、次の規則もまとめて定義している。
    ・合同規則 (congruence rules)    : 部分項が簡約できれば、それを含む項も簡約できる。
    ・反射律 RId (closure rules)     : 0 ステップの簡約。
    ・推移律 RTrans (closure rules)  : 簡約を 2 つつなげる。
  そのため、ReduceK e e′ などは 0 ステップ以上の簡約 (⟶*) を表す。
  論文の規則と、定義されている場所の対応:
    (β.v), (β.let), (β.S), (β.R) : ReduceK
    (η.v)                        : ReduceVK
    (η.let)                      : ReduceCK
  (let.1), (let.2), (assoc) に対応する規則は無い。
  DSKernel 言語の項は、すでに部分式に名前が付いた形だからである（論文 p.6）。
-}

mutual
  data ReduceK {var : typK → Set} : {τ₁ : typK} → {Δ : conttypK} →
               termK[ var , Δ ] τ₁ →
               termK[ var , Δ ] τ₁ → Set where
    -- (β.v) K ((λx.M) V) -> M[x:=V][k:=K]
    -- 値の代入 SubstK と、継続の代入 SubstK₂ を順に行う。
    RBetaV  : {τ₁ τ₂ τ₃ τ₄ : typK} → {Δ : conttypK} →
              {e₁ : var τ₂ → termK[ var , K τ₁ ▷ τ₃ ] τ₄} →
              {v : valueK[ var ] τ₂} →
              {c : pcontextK[ var , Δ , τ₁ ] τ₃} →
              {e₁′ : termK[ var , K τ₁ ▷ τ₃ ] τ₄} →
              {e₂ : termK[ var , Δ ] τ₄} →
              SubstK e₁ v e₁′ →
              SubstK₂ e₁′ c e₂ →
              ReduceK (App (Fun (λ x → e₁ x)) v c) e₂
    -- (β.let) let x = V in M -> M[x:=V]
    -- コンテキスト let x = [] in M の穴に値 V が入った形 K[V] を簡約する。
    RBetaLet : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {e  : var τ₁ → termK[ var , Δ ] τ₂} →
              {v  : valueK[ var ] τ₁} →
              {e′ : termK[ var , Δ ] τ₂} →
              SubstK e v e′ →
              ReduceK (Ret (KLet e) v) e′
    -- (β.S) K <J[S V]> -> K <V (λy.<J[y]>)>
    -- j は reset 直下の継続（Δ = • τ₄）なので、[]• か let x = [] in M• の形をしている。
    -- λy.<J[y]> は、本体が [<J[y]>]k の形の λ 抽象になる。
    RShift  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typK} → {Δ : conttypK} →
              {v  : valueK[ var ]
                    ((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])} →
              {j  : pcontextK[ var , • τ₄ , τ₁ ] τ₂} →
              {k : pcontextK[ var , Δ , τ₅ ] τ₆} →
              ReduceK (RetE k (App Shift v j))
                      (RetE k (App v (Fun (λ y → RetE KVar (Ret j (Var y))))
                                   KId))
    -- K <J[Sk.M]> -> K <(λk.M) (λy.<J[y]>)>
    -- RShift の Sk.M 版（論文には無い）。
    RShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typK} → {Δ : conttypK} →
              {e  : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) →
                    termK[ var ,  K τ₄ ▷ τ₄ ] τ₅} →
              {j  : pcontextK[ var , • τ₄ , τ₁ ] τ₂} →
              {k : pcontextK[ var , Δ , τ₅ ] τ₆} →
              ReduceK (RetE k (Shift2 e j))
                      (RetE k (App (Fun e)
                                   (Fun (λ y → RetE KVar (Ret j (Var y))))
                                   KId))
    -- (β.R) k <V> -> k V
    -- reset の中身が [V]• になったら reset を外す。
    RReset  : {τ₁ τ₂ : typK} → {Δ : conttypK} →
              {v : valueK[ var ] τ₁} →
              {k : pcontextK[ var , Δ , τ₁ ] τ₂} →
              ReduceK (RetE k (Ret KId v)) (Ret k v)

    -- congruence rules
    -- 部分項（値・コンテキスト・reset の中身・λ の本体など）が簡約できれば、
    -- それを含む項も簡約できる、という規則。
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
    -- (η.v) λx.V x -> V
    -- λ の本体は [V x]k の形（App v (Var x) KVar）。
    -- 受け取った値 x を、そのまま V に渡すだけの関数は、V 自身に簡約できる。
    -- （論文の条件 x ∉ fv(V) は、V が λ x → の外側で与えられていて、
    -- V の中に x が現れようがないことで、自動的に満たされている。）
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
    -- (η.let) let x = [] in K x -> K
    -- 受け取った値 x をそのまま K に渡すだけのコンテキストは、K 自身に簡約できる。
    -- （論文の条件 x ∉ fv(K) は、K が λ x → の外側で与えられていて、
    -- K の中に x が現れようがないことで、自動的に満たされている。）
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

{-
  ----------------------------------------------------------------------------
  簡約の等式推論用の記法
  ----------------------------------------------------------------------------
  DSterm.agda の Reasoning と同じもの。
-}

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

{-
  ----------------------------------------------------------------------------
  代入に関する補題
  ----------------------------------------------------------------------------
  代入される変数が現れない場合、代入しても何も変わらない、という補題。
  つまり、x が現れない v₁, e₁, k₁ について、
  v₁[x:=v] = v₁、e₁[x:=v] = e₁、k₁[x:=v] = k₁ が成り立つ。
-}

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

-- []k に []k を代入しても何も変わらない。
-- つまり、e[k:=[]k] = e。
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
