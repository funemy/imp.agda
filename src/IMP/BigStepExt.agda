{-# OPTIONS --guardedness #-}

-- This module is defined similar to IMP.SmallStepExt, describing
-- divergence in big-step semantics.
module IMP.BigStepExt where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import IMP.Base
open import IMP.Syntax
open import IMP.BigStep
open import Relation.Binary.PropositionalEquality using (_≡_)

mutual
    PremisesOf : Stm → State → Set
    PremisesOf (assign x aexp) σ = ⊥
    PremisesOf skip σ = ⊥
    PremisesOf (seq stm1 stm2) σ =
        [ stm1 , σ ]⇓∞
        ⊎
        ∃[ σ' ] [ stm1 , σ ]⇓ just σ' × [ stm2 ,  σ' ]⇓∞
    PremisesOf (ite p stm1 stm2) σ =
        B⟦ p ⟧ σ ≡ just true × [ stm1 , σ ]⇓∞
        ⊎
        B⟦ p ⟧ σ ≡ just false × [ stm2 , σ ]⇓∞
    PremisesOf (whiledo p stm) σ =
        B⟦ p ⟧ σ ≡ just true × [ stm ⨾ whiledo p stm , σ ]⇓∞

    record [_,_]⇓∞ (stm : Stm) (σ : State) : Set where
        coinductive
        field
            premises : PremisesOf stm σ