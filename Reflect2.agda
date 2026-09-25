{-# OPTIONS --rewriting #-}

module Reflect2 where

open import CPSterm
open import DSterm
open import DStermK
open import DSTrans
open import Embed
open import Reflect2a
open import Reflect2b
-- open import Reflect2c
open import CPSColonTrans hiding (cpsT)

open import Function
open import Relation.Binary.PropositionalEquality

-- main theorem

maincorrectV : {var : cpstyp → Set} {τ₁ : cpstyp} →
               (v : cpsvalue[ var ] τ₁) →
               cpsV (knormalV (embedV (dsV v))) ≡ v
maincorrectV {var} v rewrite Reflect2b.correctV {var ∘ cpsT} (dsV v) =
  Reflect2a.correctV v

maincorrect : {var : cpstyp → Set} {τ τ₁ τ₂ : cpstyp} →
              (e : cpsterm[ var , K τ₁ ⇒ τ₂ ] τ) →
              cpsE (knormal (embed (dsE e)) KVar) ≡ e
maincorrect {var} e rewrite Reflect2b.correct {var ∘ cpsT} (dsE e) =
  Reflect2a.correct e

maincorrect2 : {var : cpstyp → Set} {τ τ₁ : cpstyp} →
               (e : cpsterm[ var , • τ₁ ] τ) →
               cpsE (knormal (embed (dsE e)) KId) ≡ e
maincorrect2 {var} e rewrite Reflect2b.correct2 {var ∘ cpsT} (dsE e) =
  Reflect2a.correct e
