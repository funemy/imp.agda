{-# OPTIONS --guardedness #-}

-- This module is defined similar to IMP.SmallStepExt, describing
-- divergence in big-step semantics.
module IMP.BigStepExt where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Syntax
open import IMP.BigStep
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation using (¬_)

-- This is a refinement over `Stm` to characterize statements that may diverge.
data MayDiverge : State → Stm → Set where
    maydiv-seq1 :
        { σ : State } →
        { stm1 stm2 : Stm } →
        MayDiverge σ (seq stm1 stm2)
    maydiv-seq2 :
        { σ σ' : State } →
        { stm1 stm2 : Stm } →
        [ stm1 , σ ]⇓ just σ' →
        MayDiverge σ (seq stm1 stm2)
    maydiv-ite-tt :
        { σ : State } →
        { p : Bexp } →
        { stm1 stm2 : Stm } →
        B⟦ p ⟧ σ ≡ just true →
        MayDiverge σ (ite p stm1 stm2)
    maydiv-ite-ff :
        { σ : State } →
        { p : Bexp } →
        { stm1 stm2 : Stm } →
        B⟦ p ⟧ σ ≡ just false →
        MayDiverge σ (ite p stm1 stm2)
    maydiv-while :
        { σ : State } →
        { p : Bexp } →
        { stm : Stm } →
        B⟦ p ⟧ σ ≡ just true →
        MayDiverge σ (whiledo p stm)

MayDivergeStm : State → Set
MayDivergeStm σ = ∃[ stm ] (MayDiverge σ stm)

mutual
    SubDerivOf : {σ : State} → MayDivergeStm σ → Set
    SubDerivOf (seq stm1 stm2 , maydiv-seq1 {σ}) = [ stm1 , σ ]⇑
    SubDerivOf (seq stm1 stm2 , maydiv-seq2 {σ' = σ'} _) = [ stm2 , σ' ]⇑
    SubDerivOf (ite p stm1 stm2 , maydiv-ite-tt {σ} _) = [ stm1 , σ ]⇑
    SubDerivOf (ite p stm1 stm2 , maydiv-ite-ff {σ} _) = [ stm2 , σ ]⇑
    SubDerivOf (whiledo p stm , maydiv-while {σ} _) = [ stm ⨾ whiledo p stm , σ ]⇑

    record [_,_]⇑ (stm : Stm) (σ : State) : Set where
        coinductive
        field
            subderiv : (pre : MayDiverge σ stm) → SubDerivOf (stm , pre)

open [_,_]⇑ public

-- skip definitely won't diverge
skip-no-div : ∀ {σ : State} → ¬ MayDiverge σ skip
skip-no-div ()

-- Soundness of the "may diverge" judgement defined above
-- (or really, the soundness of its negation "must not diverge"),
-- i.e., if a statement must not diverge, then there is a terminating big-step
-- interpretation.
¬maydiv-implies-⇓ :
    ∀ { σ : State } →
    (stm : Stm) →
    ¬ MayDiverge σ stm →
    ∃[ σ' ] [ stm , σ ]⇓ σ'
¬maydiv-implies-⇓ {σ} (assign x aexp) mustnotdiv with A⟦ aexp ⟧ σ in eq
... | just a = just (σ [ x := a ]) , b-assign eq
... | nothing = exn , b-assign-⊥ eq
¬maydiv-implies-⇓ skip mustnotdiv = just _ , b-skip
¬maydiv-implies-⇓ (seq stm1 stm2) mustnotdiv = ⊥-elim (mustnotdiv maydiv-seq1)
¬maydiv-implies-⇓ {σ} (ite p stm1 stm2) mustnotdiv with B⟦ p ⟧ σ in eq
... | just false = ⊥-elim (mustnotdiv (maydiv-ite-ff eq))
... | just true = ⊥-elim (mustnotdiv (maydiv-ite-tt eq))
... | nothing = exn , b-ite-⊥ eq
¬maydiv-implies-⇓ {σ} (whiledo p stm) mustnotdiv with B⟦ p ⟧ σ in eq
... | just false = just σ , b-whiledo-ff eq
... | just true = ⊥-elim (mustnotdiv (maydiv-while eq))
... | nothing = exn , b-whiledo-⊥₁ eq

-- This is not provable, otherwise we solved halting problem?
-- skip-no-div' : ∀ (σ : State) → ¬ [ skip , σ ]⇑
-- skip-no-div' σ = {!   !}

-- assign definitely won't diverge
assign-no-div : ∀ (σ : State) (x : SSymbol) (a : Aexp) → ¬ MayDiverge σ (assign x a)
assign-no-div σ x a ()

whiletrue-div : ∀ (σ : State) → [ (WHILE tt DO skip) , σ ]⇑
whiletrue-div σ .subderiv (maydiv-while p) .subderiv maydiv-seq1 .subderiv ()
whiletrue-div σ .subderiv (maydiv-while p) .subderiv (maydiv-seq2 {σ' = σ'} x) = whiletrue-div σ'