-- This module defines an alternative version of small-step semantics,
-- where the end of a computation is denoted by (skip , σ), and there
-- is no exception.
--
-- NOTE: This module is only for experiment.
module IMP.SmallStep.NoExn where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Examples
open import IMP.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

Config : Set
Config = Stm × State

data [_,_]⟶_ : (stm : Stm) → (σ : State) → (γ : Config) → Set where
    s-assign :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : State } →
        { v : Value } →
        A⌊ aexp ⌋ σ ≡ v →
    -----------------------------------------------------------------
        [ assign x aexp , σ ]⟶ (skip , (σ [ x := v ]))

    s-skip :
        { σ : State } →
    -----------------------------------------------------------------
        [ skip , σ ]⟶ (skip , σ)

    s-seq-1 :
        { stm1 stm2 stm1' : Stm } →
        { σ σ' : State } →
        [ stm1 , σ ]⟶ (stm1' , σ' ) →
    -----------------------------------------------------------------
        [ seq stm1 stm2 , σ ]⟶ (seq stm1' stm2 , σ')

    s-seq-2 :
        { stm1 stm2 : Stm } →
        { σ σ' : State } →
        [ stm1 , σ ]⟶ (skip , σ') →
    -----------------------------------------------------------------
        [ seq stm1 stm2 , σ ]⟶ (stm2 , σ')

    s-ite-tt :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        B⌊ b ⌋ σ ≡ true →
    -----------------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⟶ (stm1 , σ)

    s-ite-ff :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        B⌊ b ⌋ σ ≡ false →
    -----------------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⟶ (stm2 , σ)

    s-while-tt :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⌊ b ⌋ σ ≡ true →
    ---------------------------------------------------------------------
        [ whiledo b stm , σ ]⟶ (seq stm (whiledo b stm) , σ)

    s-while-ff :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⌊ b ⌋ σ ≡ false →
    ---------------------------------------------------------------------
        [ whiledo b stm , σ ]⟶ (skip , σ)

-- Derivation sequence (finite), or dseq
-- Note that, by definition, this sequence cannot raise exceptions, because
-- the sequence is constructed backwards from the end, which is a single-step
-- into a well-formed state (instead of an exception).
infix 4 [_,_]⟶*_
data [_,_]⟶*_ : (stm : Stm) → (σ : State) → (σ' : State) → Set where
    dseq-id :
        { σ : State } →
        [ skip , σ ]⟶ (skip , σ) →
    -----------------------------------------------------------------
        [ skip , σ ]⟶* σ

    dseq-cons :
        { stm stm' : Stm } →
        { σ σ' σ'' : State } →
        [ stm , σ ]⟶ (stm' , σ'' ) →
        [ stm' , σ'' ]⟶* σ' →
    -----------------------------------------------------------------
        [ stm , σ ]⟶* σ'

test : [ prog1 , σ₀ ]⟶* σ-prog1
test =
    dseq-cons
        (s-seq-2 (s-assign refl))
        (dseq-cons
            (s-while-tt refl)
            (dseq-cons
                (s-seq-2 (s-assign refl))
                (dseq-cons
                    (s-while-tt refl)
                    (dseq-cons
                        (s-seq-2 (s-assign refl))
                        (dseq-cons
                            (s-while-ff refl)
                            (dseq-id s-skip))))))