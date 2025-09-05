{-# OPTIONS --guardedness #-}

-- This module is defined similar to IMP.SmallStepExt, describing
-- divergence in big-step semantics.
module IMP.BigStepExt where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product.Base using (∃-syntax; _×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Syntax
open import IMP.BigStep
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Negation using (¬_)

-- This is a refinement over `Stm` to characterize statements that can potentially diverge.
data MayDiverge : State → Stm → Set where
    may-div-seq1 :
        { σ : State } →
        { stm1 stm2 : Stm } →
        MayDiverge σ (seq stm1 stm2)
    may-div-seq2 :
        { σ σ' : State } →
        { stm1 stm2 : Stm } →
        [ stm1 , σ ]⇓ just σ' →
        MayDiverge σ (seq stm1 stm2)
    may-div-ite-tt :
        { σ : State } →
        { p : Bexp } →
        { stm1 stm2 : Stm } →
        B⟦ p ⟧ σ ≡ just true →
        MayDiverge σ (ite p stm1 stm2)
    may-div-ite-ff :
        { σ : State } →
        { p : Bexp } →
        { stm1 stm2 : Stm } →
        B⟦ p ⟧ σ ≡ just false →
        MayDiverge σ (ite p stm1 stm2)
    may-div-while :
        { σ : State } →
        { p : Bexp } →
        { stm : Stm } →
        B⟦ p ⟧ σ ≡ just true →
        MayDiverge σ (whiledo p stm)

MayDivergeStm : State → Set
MayDivergeStm σ = Σ Stm (MayDiverge σ)

mutual
    SubDerivOf : {σ : State} → MayDivergeStm σ → Set
    SubDerivOf (seq stm1 stm2 , may-div-seq1 {σ}) = [ stm1 , σ ]⇓∞
    SubDerivOf (seq stm1 stm2 , may-div-seq2 {σ' = σ'} _) = [ stm2 , σ' ]⇓∞
    SubDerivOf (ite p stm1 stm2 , may-div-ite-tt {σ} _) = [ stm1 , σ ]⇓∞
    SubDerivOf (ite p stm1 stm2 , may-div-ite-ff {σ} _) = [ stm2 , σ ]⇓∞
    SubDerivOf (whiledo p stm , may-div-while {σ} _) = [ stm ⨾ whiledo p stm , σ ]⇓∞

    record [_,_]⇓∞ (stm : Stm) (σ : State) : Set where
        coinductive
        field
            subderiv : { pre : MayDiverge σ stm } → SubDerivOf (stm , pre)

open [_,_]⇓∞ public

eval∞ : (stm : Stm) → (σ : State) → [ stm , σ ]⇓∞
subderiv (eval∞ (seq stm1 stm2) σ) {may-div-seq1} = eval∞ stm1 σ
subderiv (eval∞ (seq stm1 stm2) σ) {may-div-seq2 _} = eval∞ stm2 _
subderiv (eval∞ (ite p stm1 stm2) σ) {may-div-ite-tt _} = eval∞ stm1 σ
subderiv (eval∞ (ite p stm1 stm2) σ) {may-div-ite-ff _} = eval∞ stm2 σ
subderiv (eval∞ (whiledo p stm) σ) {may-div-while x} = eval∞ (seq stm (whiledo p stm)) σ
