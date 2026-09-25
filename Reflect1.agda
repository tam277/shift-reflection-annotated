{-# OPTIONS --rewriting #-}

module Reflect1 where

open import CPSterm
open import DSterm hiding (conttyp)
open import DStermK
open import DSTrans
open import Embed
open import Reflect1a
open import Reflect1b
open import CPSColonTrans hiding (cpsT)

open import Function
open import Relation.Binary.PropositionalEquality

-- main theorem

maincorrectV : {var : typ → Set} {τ₁ β : typ} →
               (v : value[ var ] τ₁) →
               Reduce {β = β} (Val v)
                               (Val (embedV (dsV (cpsV (knormalV v)))))
maincorrectV {var} v
  rewrite Reflect1b.correctV {var ∘ embedT ∘ dsT} (knormalV v) =
  Reflect1a.correctV v

maincorrect : {var : cpstyp → Set} {τ₁ α β : typ} {Δ : conttyp} →
              (e : term[ var ∘ cpsT ∘ knormalT , α ▷ β ] τ₁) →
              (k : cpscont[ var , Δ , cpsT (knormalT α) ] cpsT (knormalT β)) →
              Reduce (plug (embedC (dsC k)) e)
                     (embed (dsE (cpsE (knormal e (dsC k)))))
maincorrect {var} e k rewrite Reflect1b.correct (knormal e (dsC k)) =
  Reflect1a.correct {var ∘ cpsT} e (dsC k)
