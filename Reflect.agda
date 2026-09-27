{-
  ============================================================================
  全体をまとめたファイル
  ============================================================================
  DS 言語と CPS 言語の間の reflection（論文 定義 1）の 4 つの性質を、
  それぞれ証明したファイルを import する。
    Reflect1 : Reflection (1)  M ⟶* M*#            （論文 系 28）
    Reflect2 : Reflection (2)  N#* = N             （論文 系 29）
    Reflect3 : Reflection (3)  M ⟶ M′ ならば M* ⟶* M′*  （論文 系 30）
    Reflect4 : Reflection (4)  N ⟶ N′ ならば N# ⟶* N′#  （論文 系 31）
  さらに、コロン変換の分解 DecomposeColon も import する。
  このファイルを型検査すれば、すべての証明が型検査される。
  ============================================================================
-}

{-# OPTIONS --rewriting #-}

module Reflect where

open import Reflect1
open import Reflect2
open import Reflect3
open import Reflect4

-- have to place at last, since the rewrite rule in DecomposeColon causes
-- unsolvable constraints in Reflect3
open import DecomposeColon
