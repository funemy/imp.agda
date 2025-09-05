{-# OPTIONS --guardedness #-}

-- This module is defined similar to IMP.SmallStepExt, describing
-- divergence in big-step semantics.
module IMP.BigStepExt where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Syntax
open import IMP.BigStep
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation using (¬_)

-- This is a refinement over `Stm` to characterize statements that may diverge.
data Diverge : State → Stm → Set where
    div-seq1 :
        { σ : State } →
        { stm1 stm2 : Stm } →
        Diverge σ (seq stm1 stm2)
    div-seq2 :
        { σ σ' : State } →
        { stm1 stm2 : Stm } →
        [ stm1 , σ ]⇓ just σ' →
        Diverge σ (seq stm1 stm2)
    div-ite-tt :
        { σ : State } →
        { p : Bexp } →
        { stm1 stm2 : Stm } →
        B⟦ p ⟧ σ ≡ just true →
        Diverge σ (ite p stm1 stm2)
    div-ite-ff :
        { σ : State } →
        { p : Bexp } →
        { stm1 stm2 : Stm } →
        B⟦ p ⟧ σ ≡ just false →
        Diverge σ (ite p stm1 stm2)
    div-while :
        { σ : State } →
        { p : Bexp } →
        { stm : Stm } →
        B⟦ p ⟧ σ ≡ just true →
        Diverge σ (whiledo p stm)

DivergeStm : State → Set
DivergeStm σ = ∃[ stm ] (Diverge σ stm)

mutual
    SubDerivOf : {σ : State} → DivergeStm σ → Set
    SubDerivOf (seq stm1 stm2 , div-seq1 {σ}) = [ stm1 , σ ]⇑
    SubDerivOf (seq stm1 stm2 , div-seq2 {σ' = σ'} _) = [ stm2 , σ' ]⇑
    SubDerivOf (ite p stm1 stm2 , div-ite-tt {σ} _) = [ stm1 , σ ]⇑
    SubDerivOf (ite p stm1 stm2 , div-ite-ff {σ} _) = [ stm2 , σ ]⇑
    SubDerivOf (whiledo p stm , div-while {σ} _) = [ stm ⨾ whiledo p stm , σ ]⇑

    record [_,_]⇑ (stm : Stm) (σ : State) : Set where
        coinductive
        field
            subderiv : (pre : Diverge σ stm) → SubDerivOf (stm , pre)

open [_,_]⇑ public

eval⇑ : (stm : Stm) → (σ : State) → [ stm , σ ]⇑
eval⇑ (seq stm1 stm2) σ .subderiv div-seq1 = eval⇑ stm1 σ
eval⇑ (seq stm1 stm2) σ .subderiv (div-seq2 _) = eval⇑ stm2 _
eval⇑ (ite p stm1 stm2) σ .subderiv (div-ite-tt _) = eval⇑ stm1 σ
eval⇑ (ite p stm1 stm2) σ .subderiv (div-ite-ff _) = eval⇑ stm2 σ
eval⇑ (whiledo p stm) σ .subderiv (div-while _) = eval⇑ (seq stm (whiledo p stm)) σ

-- As it shown by the following example, what's defined above is a "may diverge" judgement.
_ : [ skip , σ₀ ]⇑
_ = eval⇑ skip σ₀

-- skip definitely won't diverge
skip-no-div : ∀ (σ : State) → ¬ Diverge σ skip
skip-no-div σ ()

-- This is not provable, otherwise we solved halting problem?
-- skip-no-div' : ∀ (σ : State) → ¬ [ skip , σ ]⇑
-- skip-no-div' σ = {!   !}

-- assign definitely won't diverge
assign-no-div : ∀ (σ : State) (x : SSymbol) (a : Aexp) → ¬ Diverge σ (assign x a)
assign-no-div σ x a ()

whiletrue-div : ∀ (σ : State) → [ (WHILE tt DO skip) , σ ]⇑
whiletrue-div σ .subderiv (div-while p) .subderiv div-seq1 .subderiv ()
whiletrue-div σ .subderiv (div-while p) .subderiv (div-seq2 {σ' = σ'} x) = whiletrue-div σ'