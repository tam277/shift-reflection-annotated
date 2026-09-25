{-# OPTIONS --rewriting #-}

module Reflect where

open import Reflect1
open import Reflect2
open import Reflect3
open import Reflect4

-- have to place at last, since the rewrite rule in DecomposeColon causes
-- unsolvable constraints in Reflect3
open import DecomposeColon
