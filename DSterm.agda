{-
  ============================================================================
  DS 言語 (論文 2.1 節)
  ============================================================================
  shift/reset と let を含む単純型付き λ 計算（DS 言語、論文では λcS）を定義するファイル。
  以下を順に定義している。
    ・型と継続の型                       (論文 p.4, 図 1 / p.5, 図 2)
    ・項（値・非値）                     (論文 p.4, 図 1)
    ・pure なコンテキストと plug          (論文 p.4, 図 1)
    ・インタプリタ                        (論文 p.4 最後の段落)
    ・代入関係                            (PHOAS 用)
    ・簡約規則                            (論文 p.4, 図 1)
    ・簡約の等式推論用の記法と補題
  型付けは項の定義に直接組み込まれていて、
  型の合う項しか書けない（論文 1.2 節）。
  ============================================================================
-}

module DSterm where

open import Data.Empty
open import Data.Nat

{-
  ----------------------------------------------------------------------------
  型の定義 (p.4, 図 1)
  ----------------------------------------------------------------------------
  論文の記法との対応:
    Nat                    : int
    τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] : τ₂ → τ₁@[τ₃, τ₄]
  関数型 τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] は、次のような関数の型。
    τ₂ 型の引数を受け取り、
    τ₁ → τ₃ 型の継続の下で実行すると、
    最終的に τ₄ 型の値を返す。
  shift を使うと答えの型が変わりうるので、戻り値の型 τ₁ だけでなく、
  継続の答えの型 τ₃ と、最終的な答えの型 τ₄ も型に含める。
-}

data typ : Set where
  Nat          : typ
  _⇒_cps[_,_] : typ → typ → typ → typ → typ

-- 継続の型。τ₁ ▷ τ₂ は論文の継続の型 δ = τ₁ → τ₂ にあたり、
-- 「τ₁ 型の値を受け取って τ₂ 型の答えを返す継続」を表す。
data conttyp : Set where
  _▷_ : typ → typ → conttyp

infix 15 _▷_
infix 17 _⇒_cps[_,_]

{-
  ----------------------------------------------------------------------------
  項の定義 (p.4, 図 1。型規則は p.5, 図 2)
  ----------------------------------------------------------------------------
  論文の構文 M ::= V | P のとおり、項 M は値 V か非値 P のどちらかである。
  Agda でも、項 term は Val と NonVal の 2 つのコンストラクタからなり、
  それぞれ値 value と非値 nonvalue を包む。
    term[ var , τ₁ ▷ τ₂ ] τ₃    : 項 M               (論文の Γ ⊢ M : [τ₁, τ₂] τ₃)
                                  τ₁ 型の値を返し、
                                  τ₁ → τ₂ 型の継続の下で実行すると、
                                  最終的に τ₃ 型の答えを返す
    value[ var ] τ              : 値 V               (論文の Γ ⊢v V : τ)
    nonvalue[ var , Δ ] τ       : 非値 P（関数適用, shift, reset, let）
  値と非値を分けて定義しているのは、
  (let.1), (let.2) などの簡約規則や CPS 変換で、
  値の場合とそうでない場合を区別したくなるため（論文 p.3）。
  （Agda 上では value, term, nonvalue の順に定義しているが、
  3 つは mutual で互いに参照しあっているので、定義の順番に意味はない。）

  束縛は PHOAS (Parameterized Higher-Order Abstract Syntax) で表す（論文 1.2 節）。
  var : typ → Set は「τ 型の変数」を表す型で、
  λx.M の本体は「var τ を受け取って項を返す Agda の関数」として書く。
  型環境 Γ は明示的には現れず、Agda の関数の束縛がその役割を果たす。
-}

mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    -- 変数 x。PHOAS なので var τ₁ 型の Agda の値をそのまま包む。(TVAR)
    Var   : {τ₁ : typ} → var τ₁ → value[ var ] τ₁
    -- n
    Num   : ℕ → value[ var ] Nat
    -- λ 抽象 λx.M。(TFUN)
    -- 本体 M の型 [τ₁, τ₃] τ₄ が、そのまま関数型 τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] に現れる。
    Fun   : {τ₁ τ₂ τ₃ τ₄ : typ} →
            (var τ₂ → term[ var , τ₁ ▷ τ₃ ] τ₄) →
            value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])
    -- shift 演算子 S。(TSHIFT)
    -- 論文と同じく shift は専用の構文ではなく定数（値）として定義し、
    -- S (λk.M) の形で使う（論文 p.3）。
    -- S は「捕まえた継続を受け取る関数」を引数に取る:
    --   ((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])
    --     ^^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^
    --     捕まえた継続 k の型        shift の本体 M の型
    -- ・k の型の答えの型が τ₃ , τ₃ と同じなのは、
    --   k を呼び出すと、その中身が reset で囲まれた形で実行されるため。
    --   （k の呼び出し自体は、外側の答えの型を変えない。）
    -- ・本体の型が τ₄ cps[ τ₄ , _ ] なのは、
    --   本体が恒等継続の下で実行されるため。
    --   （インタプリタ gv Shift の (λ x → x) を参照。）
    -- S (λk.M) 全体は、S を呼んだ箇所の継続 τ₁ → τ₂ を k として捕まえ、
    -- 最終的に本体の答え τ₅ を返す。
    Shift : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
            value[ var ] (((τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) ⇒ τ₄ cps[ τ₄ , τ₅ ])
                          ⇒ τ₁ cps[ τ₂ , τ₅ ])

  -- term : 値か非値。
  data term[_,_]_ (var : typ → Set) : conttyp → typ → Set where
    -- 値 V を項として使う。(TVAL)
    -- 値はそのまま継続に渡されるだけなので、
    -- 項全体の答えの型は、継続の答えの型 τ₂ と一致する。
    Val    : {τ₁ τ₂ : typ} →
             value[ var ] τ₁ →
             term[ var , τ₁ ▷ τ₂ ] τ₂
    -- 非値 P を項として使う。
    NonVal : {τ : typ} {Δ : conttyp} →
             nonvalue[ var , Δ ] τ →
             term[ var , Δ ] τ

  -- nonvalue : 値でない項。
  data nonvalue[_,_]_ (var : typ → Set) : conttyp → typ → Set where
    -- 関数適用 M N。(TAPP)
    -- M を先に評価し、次に N を評価し、最後に関数を呼ぶ。
    -- 答えの型に注目すると、
    --   関数呼び出しの継続が τ₃ を返す
    --   → 関数呼び出しが τ₄ を返す
    --   → N の評価が τ₅ を返す
    --   → M の評価が τ₆ を返す
    -- と、評価の順序を逆にたどる形で τ₃ τ₄ τ₅ τ₆ が受け渡されている。
    App   : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
            term[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆ →
            term[ var , τ₂ ▷ τ₄ ] τ₅ →
            nonvalue[ var , τ₁ ▷ τ₃ ] τ₆
    -- Sk.M の形の shift。
    -- shift を定数 S ではなく、専用の構文 (special form) として入れたもの。
    -- 論文には無く、このコードで追加したもの（README 参照）。
    -- S (λk.M) と同じ意味で、型も S (λk.M) と同じになる。
    -- （k の型は Shift の k と同じで、本体 M は恒等継続の下で実行される。）
    -- k は PHOAS の変数として、本体を表す Agda の関数の引数になる。
    Shift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
            (var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → term[ var , τ₄ ▷ τ₄ ] τ₅) →
            nonvalue[ var , τ₁ ▷ τ₂ ] τ₅
    -- reset <M>。(TRESET)
    -- M は恒等継続の下で実行されるので、M の継続の型は τ₁ ▷ τ₁。
    -- M の答え τ₂ が外側の継続に渡されるので、
    -- reset 全体は、値と同じ形の型 [τ₂, τ₃] τ₃ になる。
    -- （reset の外から見ると、答えの型は変わらない。）
    Reset : {τ₁ τ₂ τ₃ : typ} →
            term[ var , τ₁ ▷ τ₁ ] τ₂ →
            nonvalue[ var , τ₂ ▷ τ₃ ] τ₃
    -- let x = M in N。(TLET)
    -- M を評価して x に束縛し、N を評価する。
    -- N は変数を受け取る Agda の関数で表している（PHOAS）。
    -- M の継続は「x に束縛して N を実行する」ことなので、
    -- その答えの型は、N 全体の答えの型 τ₄ になる。
    Let   : {τ₁ τ₄ τ₅ : typ} {τ₂▷τ₃ : conttyp} →
            term[ var , τ₁ ▷ τ₄ ] τ₅ →                -- M
            (var τ₁ → term[ var , τ₂▷τ₃ ] τ₄) →    -- λx. N
            nonvalue[ var , τ₂▷τ₃ ] τ₅
            -- τ₂▷τ₃ を τ₂ ▷ τ₃ にすると、のちに embedContT できなくなる
            -- （τ₂▷τ₃ は空白の無い 1 つの変数名で、
            --   N の継続の型を「_ ▷ _ の形」に分解せず、そのまま受け渡している。）

{-
  ----------------------------------------------------------------------------
  pure なコンテキスト (p.4, 図 1)
  ----------------------------------------------------------------------------
  論文の pure contexts にあたる。
    J, K ::= [] | K[[] M] | K[V []] | K[let x = [] in M]
  pure とは、穴が reset で囲まれていないということ。
  (β.S) 規則 <J[S V]> ⟶ ... で、直近の reset までの継続 J を表すのに使う。

  コンテキストは inside-out の形で定義されている。
  outside-in の形との違いや、inside-out にしている理由は、論文 p.11 を参照。

  pcontext[ var , Δ , τ₁ ] τ₂ の読み方:
    τ₁ ▷ τ₂ : 穴に入る項の継続の型
    Δ       : 穴を埋めた後の項全体の継続の型
  pure なので、穴に入る項の答えの型と、全体の答えの型は同じ。
  （plug の型の τ₃ を参照。）
-}

data pcontext[_,_,_]_ (var : typ → Set) : conttyp → typ → typ → Set where
  -- []
  Hole  : {τ₁ τ₂ : typ} →
          pcontext[ var , τ₁ ▷ τ₂ , τ₁ ] τ₂
  -- K[[] M]
  App₁  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {Δ : conttyp} →
          pcontext[ var , Δ , τ₁ ] τ₃ →
          term[ var , τ₂ ▷ τ₄ ] τ₅ →
          pcontext[ var , Δ , τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] ] τ₅
  -- K[V []]
  App₂  : {τ₁ τ₂ τ₃ τ₄ : typ} {Δ : conttyp} →
          value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) →
          pcontext[ var , Δ , τ₁ ] τ₃ →
          pcontext[ var , Δ , τ₂ ] τ₄
  -- K[Let x = [] in M]
  Let   : {τ₁ τ₂ τ₃ τ₄ : typ} {Δ : conttyp} →
          pcontext[ var , Δ , τ₁ ] τ₃ →                -- K
          (var τ₂ → term[ var , τ₁ ▷ τ₃ ] τ₄) →        -- λx. M
          pcontext[ var , Δ , τ₂ ] τ₄

-- plug k e : コンテキスト k の穴を項 e で埋めた項 K[e]。
-- inside-out なので、e を内側から 1 段ずつ包んでいき、最後に外側の k に渡す。
plug : {var : typ → Set} → {τ₁ τ₂ τ₃ : typ} {τ₄▷τ₅ : conttyp} →
       pcontext[ var , τ₄▷τ₅ , τ₁ ] τ₂ →
       term[ var , τ₁ ▷ τ₂ ] τ₃ →
       term[ var , τ₄▷τ₅ ] τ₃
plug Hole e = e
plug (App₁ k e₂) e = plug k (NonVal (App e e₂))
plug (App₂ v₁ k) e = plug k (NonVal (App (Val v₁) e))
plug (Let k e₂) e = plug k (NonVal (Let e e₂))

{-
  ----------------------------------------------------------------------------
  項の例
  ----------------------------------------------------------------------------
  型が付くことを確かめるための例。
  CPSColonTrans.agda で、CPS 変換のテストにも使われている。
  ' の付いた版は、同じ項を別の書き方（Sk.M や let）で書いたもの。
-}

-- λx.x
val1 : {var : typ → Set} → {τ₁ τ₂ : typ} →
       value[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val1 = Fun (λ x → Val (Var x))

-- λx.S(λk.k x)
val2 : {var : typ → Set} → {τ₁ τ₂ : typ} →
       value[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val2 = Fun (λ x → NonVal (App (Val Shift)
         (Val (Fun (λ k → NonVal (App (Val (Var k)) (Val (Var x))))))))

-- λx.Sk.k x（val2 を Shift2 で書いたもの）
val2' : {var : typ → Set} → {τ₁ τ₂ : typ} →
        value[ var ] (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
val2' = Fun (λ x → NonVal (Shift2 (λ k →
          NonVal (App (Val (Var k)) (Val (Var x))))))

-- λx.S(λk.x)
-- k を使わずに捨てるので、答えの型が τ₃ から τ₁ に変わる例。
-- 捕まえた継続の答えの型 τ は型から決まらないので、明示的に与えている。
val3 : {var : typ → Set} → {τ₁ τ₂ τ₃ τ : typ} →
       value[ var ] (τ₁ ⇒ τ₂ cps[ τ₃ , τ₁ ])
val3 {τ = τ} = Fun (λ x → NonVal (App (Val (Shift {τ₃ = τ}))
                                        (Val (Fun (λ k → Val (Var x))))))

-- λx.Sk.x（val3 を Shift2 で書いたもの）
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
-- val4 の部分式に let で名前を付けた形（A-正規形）。型は val4 と同じ。
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
-- val4' を plug を使って書いたもの。
-- 一番内側で Hole に m n を入れているため、τ₃ = τ₄ に制限された型になっている。
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

{-
  ----------------------------------------------------------------------------
  インタプリタ (論文 p.4 最後の段落)
  ----------------------------------------------------------------------------
  型システムに基づいたインタプリタ。
  Agda で書けている（型が合っている）ことで、型健全性が成り立っていることが分かる。
  意味は CPS で与える:
    〚 τ 〛          : 型 τ の意味（Agda の型）
    gv v            : 値 v の意味
    g e k / gp e k  : 項 e を継続 k の下で実行した結果
  var として 〚_〛 を使うのが、PHOAS でインタプリタを書くときの定石。
  （変数 x : var τ が、そのまま 〚 τ 〛 の値になる。）
-}

〚_〛 : typ → Set
〚 Nat 〛 = ℕ
-- 関数は「引数と継続を受け取って答えを返す」Agda の関数になる。
〚 τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] 〛 =
   〚 τ₂ 〛 → (〚 τ₁ 〛 → 〚 τ₃ 〛) → 〚 τ₄ 〛

mutual
  gv : {τ : typ} → value[ 〚_〛 ] τ → 〚 τ 〛
  gv (Var x) = x
  gv (Num n) = n
  gv (Fun e) = λ x k → g (e x) k
  -- S は、引数 v（λk.M の意味）に次の 2 つを渡す。
  --   ・捕まえた継続 k を関数にしたもの (λ x₂ k₂ → k₂ (k x₂))
  --   ・恒等継続 (λ x → x)
  -- 捕まえた継続を呼ぶと、まず k を最後まで実行し（reset で囲まれているのと同じ）、
  -- その結果を呼び出し側の継続 k₂ に渡す。
  gv Shift = λ v k → v (λ x₂ k₂ → k₂ (k x₂)) (λ x → x)

  g : {τ₁ τ₂ τ₃ : typ} →
      term[ 〚_〛 , τ₁ ▷ τ₂ ] τ₃ → (〚 τ₁ 〛 → 〚 τ₂ 〛) → 〚 τ₃ 〛
  g (Val v) k = k (gv v)
  g (NonVal e) k = gp e k

  gp : {τ₁ τ₂ τ₃ : typ} →
       nonvalue[ 〚_〛 , τ₁ ▷ τ₂ ] τ₃ → (〚 τ₁ 〛 → 〚 τ₂ 〛) → 〚 τ₃ 〛
  -- e₁ → e₂ → 関数呼び出し、の順に実行する。
  gp (App e₁ e₂) k = g e₁ (λ v₁ → g e₂ (λ v₂ → v₁ v₂ k))
  -- gv Shift と同じ動き。
  gp (Shift2 e) k = g (e (λ x₂ k₂ → k₂ (k x₂))) (λ x → x)
  -- e を恒等継続の下で最後まで実行し、その結果を外側の継続 k に渡す。
  gp (Reset e) k = k (g e (λ x → x))
  gp (Let e₁ e₂) k = g e₁ (λ v₁ → g (e₂ v₁) k)

{-
  ----------------------------------------------------------------------------
  代入 M[x:=V]
  ----------------------------------------------------------------------------
  PHOAS では代入を関数として直接定義しにくいため、関係として定義している。
  Subst e₁ v e₂ は「e₁ の x に v を代入すると e₂ になる」、
  つまり e₁[x:=v] = e₂ と読む。
    SubstV  v₁ v v₂ : v₁[x:=v] = v₂（値への代入）
    Subst   e₁ v e₂ : e₁[x:=v] = e₂（項への代入）
    SubstNV e₁ v e₂ : e₁[x:=v] = e₂（非値への代入）
  代入される側の v₁ や e₁ は、
  「変数を受け取って項を返す Agda の関数」λ x → ... で表し、
  その x が代入される変数になる。
  各コンストラクタは、項の構造に沿って代入を中に進めていく規則になっている。
-}

mutual
  -- v₁[x:=v] = v₂
  data SubstV {var : typ → Set} : {τ₁ τ₂ : typ} →
              (var τ₁ → value[ var ] τ₂) →
              value[ var ] τ₁ →
              value[ var ] τ₂ → Set where
    -- (λx.x)[v] → v
    -- 代入される変数そのものなら v に置き換わる。
    sVar=  : {τ₁ : typ} {v : value[ var ] τ₁} →
             SubstV (λ x → Var x) v v
    -- (λ_.x)[v] → x
    -- 別の変数 x ならそのまま。
    -- PHOAS では「同じ変数か」を (λ x → Var x) と (λ _ → Var x) の形の違いで区別する。
    sVar≠  : {τ₁ τ₂ : typ} {v : value[ var ] τ₂} {x : var τ₁} →
             SubstV (λ _ → Var x) v (Var x)
    -- (λ_.n)[v] → n
    sNum   : {τ₁ : typ} {v : value[ var ] τ₁} {n : ℕ} →
             SubstV (λ _ → Num n) v (Num n)
    -- (λy.λx.ey)[v] → λx.e′
    -- λ の中に代入を進める。任意の束縛変数 x について本体の代入が成り立てばよい。
    sFun   : {τ τ₁ τ₂ τ₃ τ₄ : typ} →
             {e₁ : var τ₁ → var τ → term[ var , τ₂ ▷ τ₃ ] τ₄} →
             {v : value[ var ] τ₁} →
             {e₁′ : var τ → term[ var , τ₂ ▷ τ₃ ] τ₄} →
             ((x : var τ) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
             SubstV (λ y → Fun (e₁ y)) v (Fun e₁′)
    -- (λ_.S)[v] → S
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {v : value[ var ] τ} →
             SubstV (λ _ → Shift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅}) v Shift

  -- e₁[x:=v] = e₂
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

  -- e₁[x:=v] = e₂
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
    -- Sk.M の本体に代入を進める（k は束縛変数なので sFun と同じ扱い）。
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

-- コンテキストへの代入。
-- c₁[x:=v] = c₂
-- 項への代入と同じく、コンテキストの構造に沿って代入を中に進める。
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

{-
  ----------------------------------------------------------------------------
  代入に関する補題
  ----------------------------------------------------------------------------
  代入される変数が現れない場合（λ y → e のように y を使わない場合）、
  代入しても何も変わらない、という補題。
  つまり、x が現れない v₁ や e について、v₁[x:=v] = v₁、e[x:=v] = e が成り立つ。
  App は e₁, e₂ が値か非値かで 4 通りに場合分けしているが、
  どの場合も sApp で両方に代入を進めているだけ。
-}

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

{-
  ----------------------------------------------------------------------------
  簡約規則 (p.4, 図 1)
  ----------------------------------------------------------------------------
  Reduce e e′ は「e が 0 ステップ以上の簡約で e′ になる」(e ⟶* e′) を表す。
  1 ステップの簡約だけでなく、以下もまとめて 1 つのデータ型にしている。
    ・論文 図 1 の簡約規則 (β.v) 〜 (β.R)
    ・部分項の中で簡約してよいことを表す合同規則 (congruence rules)
    ・反射律 RId と推移律 RTrans (closure rules)
  両辺が同じ型 term[ var , τ▷α ] β を持つので、
  簡約で型が保たれること (subject reduction) が、定義から成り立っている。
-}

data Reduce {var : typ → Set} : {β : typ} {τ▷α : conttyp} →
            term[ var , τ▷α ] β →
            term[ var , τ▷α ] β → Set where
  -- (β.v) (λx.M)V -> M[x:=V]
  -- 代入は Subst 関係で表し、その証明 sub を引数に取る。
  RBetaV : {τ τ₁ τ₂ τ₃ : typ} →
           (e₁ : var τ → term[ var , τ₁ ▷ τ₂ ] τ₃) →
           (v₂ : value[ var ] τ) →
           (e₁′ : term[ var , τ₁ ▷ τ₂ ] τ₃) →
           (sub : Subst e₁ v₂ e₁′) →
           Reduce (NonVal (App (Val (Fun e₁)) (Val v₂)))
                  e₁′
  -- (η.v) λx.V x -> V
  -- 受け取った値 x を、そのまま V に渡すだけの関数は、V 自身に簡約できる。
  -- （論文の条件 x ∉ fv(V) は、V が λ x → の外側で与えられていて、
  -- V の中に x が現れようがないことで、自動的に満たされている。）
  REtaV  : {τ₁ τ₂ τ₃ τ₄ β : typ} →
           (v : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])) →
           Reduce {β = β}
                  (Val (Fun (λ x → NonVal (App (Val v) (Val (Var x))))))
                  (Val v)
  -- (β.let) let x = V in M -> M[x:=V]
  -- 束縛する項が値になったら、x に代入する。代入は Subst 関係で表す。
  RBetaLet : {τ₁ τ₄ : typ} {τ₂▷τ₃ : conttyp} →
           (v₁ : value[ var ] τ₁) →
           (e₂ : var τ₁ → term[ var , τ₂▷τ₃ ] τ₄) →
           (e₂′ : term[ var , τ₂▷τ₃ ] τ₄) →
           (sub : Subst e₂ v₁ e₂′) →
           Reduce (NonVal (Let (Val v₁) e₂))
                  e₂′
  -- (η.let) let x = M in x -> M
  -- M の結果を x に束縛して、そのまま返すだけなので、M に簡約できる。
  REtaLet : {τ₁ τ₂ τ₃ : typ} →
           (e₁ : term[ var , τ₁ ▷ τ₂ ] τ₃) →
           Reduce (NonVal (Let e₁ (λ x → Val (Var x))))
                  e₁
  -- (assoc) let y = (let x = L in M) in N -> let x = L in let y = M in N
  -- 入れ子になった let をフラットにする。
  -- （論文の条件 x ∉ fv(N) は、N が λ x → の外側で与えられていて、
  -- N の中に x が現れようがないことで、自動的に満たされている。）
  RAssoc : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {τ₇▷τ₈ : conttyp} →
           (e₁ : term[ var , τ₁ ▷ τ₂ ] τ₃) →
           (e₂ : var τ₁ → term[ var , τ₄ ▷ τ₅ ] τ₂) →
           (e₃ : var τ₄ → term[ var , τ₇▷τ₈ ] τ₅) →
           Reduce (NonVal (Let (NonVal (Let e₁ (λ x → e₂ x))) (λ y → e₃ y)))
                  (NonVal (Let e₁ (λ x → NonVal (Let (e₂ x) (λ y → e₃ y)))))
  -- (let.1) P N -> let x = P in x N
  -- 値でない関数部分 P に名前を付ける。
  -- 簡約の向きが逆に見えるが、A-正規形に近づける方向の規則（論文 p.4）。
  RLet1  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
           (e₁ : nonvalue[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) ▷ τ₅ ] τ₆) →
           (e₂ : term[ var , τ₂ ▷ τ₄ ] τ₅) →
           Reduce (NonVal (App (NonVal e₁) e₂))
                  (NonVal (Let (NonVal e₁) (λ x →
                            NonVal (App (Val (Var x)) e₂))))
  -- (let.2) V Q -> let y = Q in V y
  -- 値でない引数部分 Q に名前を付ける。
  RLet2  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
           {v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])} →
           (e₂ : nonvalue[ var , τ₂ ▷ τ₄ ] τ₅) →
           Reduce (NonVal (App (Val v₁) (NonVal e₂)))
                  (NonVal (Let (NonVal e₂) (λ y →
                            NonVal (App (Val v₁) (Val (Var y))))))
  -- (β.S) <J[S V]> -> <V (λy.<J[y]>)>
  -- 直近の reset までの pure なコンテキスト J を、λy.<J[y]> という関数にして V に渡す。
  -- j の継続の型が τ₄ ▷ τ₄ なのは、J 全体が reset の直下（恒等継続の下）にあるため。
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
  -- <J[Sk.M]> -> <(λk.M) (λy.<J[y]>)>
  -- RShift の Sk.M 版（論文には無い）。
  RShift2 : {τ₁ τ₂ τ₃ τ₄ τ₅ β : typ} →
           (e : var (τ₁ ⇒ τ₂ cps[ τ₃ , τ₃ ]) → term[ var , τ₄ ▷ τ₄ ] τ₅) →
           (j : pcontext[ var , τ₄ ▷ τ₄ , τ₁ ] τ₂) →
           Reduce {β = β}
                  (NonVal (Reset (plug j (NonVal (Shift2 e)))))
                  (NonVal (Reset (NonVal (App (Val (Fun e))
                    (Val (Fun (λ y →
                      NonVal (Reset (plug j (Val (Var y)))))))))))
  -- (β.R) <V> -> V
  -- reset の中が値になったら reset を外す。
  RReset : {τ₁ β : typ} →
           (v₁ : value[ var ] τ₁) →
           Reduce {β = β} (NonVal (Reset (Val v₁))) (Val v₁)

  -- congruence rules
  -- 部分項が簡約できれば、それを含む項も簡約できる、という規則。
  -- 次の場所で簡約できる。
  --   λ の本体 (RFun)、関数部分 (RApp₁)、関数が値のときの引数部分 (RApp₂)、
  --   let の両側 (RLet₁, RLet₂)、Sk.M の本体 (RShift₁)、reset の中 (RReset₁)。
  -- 束縛の下で簡約する規則（RFun, RLet₂, RShift₁）は、
  -- 任意の変数 x について簡約できることを要求している。
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
  -- 反射律（0 ステップ）と推移律（簡約をつなげる）。
  RId    : {β : typ} {τ▷α : conttyp } →
           {e : term[ var , τ▷α ] β} →
           Reduce e e
  RTrans : {β : typ} {τ▷α : conttyp } →
           {e₁ e₂ e₃ : term[ var , τ▷α ] β} →
           Reduce e₁ e₂ →
           Reduce e₂ e₃ →
           Reduce e₁ e₃

{-
  ----------------------------------------------------------------------------
  簡約の等式推論用の記法
  ----------------------------------------------------------------------------
  簡約の列を、途中の項を明示しながら次のように書くための記法。
    begin
      e₁
    ⟶⟨ e₁ から e₂ への簡約の証明 ⟩
      e₂
    ≡⟨ e₂ と e₃ が等しいことの証明 ⟩
      e₃
    ∎
  標準ライブラリの ≡-Reasoning と同じ使い方で、中身は RTrans と RId。
-}

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

{-
  ----------------------------------------------------------------------------
  補題
  ----------------------------------------------------------------------------
-}

-- v does not reduce to nonval e
-- 値は非値に簡約されない。
-- 値から始まる簡約規則（REtaV, RFun, RId）はどれも値を値に簡約するので、
-- Val から NonVal への簡約は RTrans を使った場合しかありえない。
-- RTrans の途中の項 e₂ が値か非値かで場合分けし、
-- どちらの場合も、より短い簡約について帰納法の仮定を使っている。
reduceVal : {var : typ → Set} {τ₁ τ₂ : typ}
            {v : value[ var ] τ₁}
            {e : nonvalue[ var , τ₁ ▷ τ₂ ] τ₂} →
            Reduce (Val v) (NonVal e) → ⊥
reduceVal (RTrans {e₂ = Val v} red₁ red₂) = reduceVal red₂
reduceVal (RTrans {e₂ = NonVal e} red₁ red₂) = reduceVal red₁

-- e -> e' => K[e] -> K[e']
-- pure なコンテキストの穴の中で簡約できる。
-- コンテキストの形ごとに合同規則 (RApp₁, RApp₂, RLet₁) を使う。
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
-- コンテキストの穴を埋めてから代入しても、
-- コンテキストと中身にそれぞれ代入してから穴を埋めても、同じになる。
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
