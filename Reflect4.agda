{-# OPTIONS --rewriting #-}

module Reflect4 where

open import CPSterm
open import DStermK
open import DSterm
open import DSTrans
open import Embed
open import Reflect4a
open import Reflect4b

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- main theorem
correctV : {var : typ → Set} {τ₁ : cpstyp} {τ : typ} →
           {v v′ : cpsvalue[ var ∘ embedT ∘ dsT ] τ₁} →
           cpsReduceV v v′ →
           Reduce {var} {τ} (Val (embedV (dsV v))) (Val (embedV (dsV v′)))
correctV red = correctVE (correctVK red)

correct : {var : typ → Set} {τ₁ : cpstyp} {Δ : CPSterm.conttyp} →
          {e e′ : cpsterm[ var ∘ embedT ∘ dsT , Δ ] τ₁} →
          cpsReduce e e′ →
          Reduce {var} (embed (dsE e)) (embed (dsE e′))
correct red = correctE (correctK red)

correctC : {var : typ → Set} {τ₃ τ₄ τ₅ : cpstyp} {Δ : CPSterm.conttyp} →
           {k k′ : cpscont[ var ∘ embedT ∘ dsT , Δ , τ₃ ] τ₄} →
           cpsReduceC k k′ →
           {e : term[ var , embedT (dsT τ₃) ▷ embedT (dsT τ₄) ]
                    embedT (dsT τ₅)} →
           Reduce {var} (plug (embedC (dsC k)) e)
                        (plug (embedC (dsC k′)) e)
correctC {τ₅ = τ₅} red = correctCE {τ₅ = dsT τ₅} (correctCK red)
