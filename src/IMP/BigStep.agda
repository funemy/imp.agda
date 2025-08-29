module IMP.BigStep where

open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just)
open import IMP.Base
open import IMP.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- big-step semantics for Statement (Stm)
data [_,_]⇓_ : (s : Stm) → (σ : State) → (σ' : Maybe State) → Set where
    b-assign :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : State } →
        { v : Value } →
        A⟦ aexp ⟧ σ ≡ just v →
    ----------------------------------------------------------
        [ assign x aexp , σ ]⇓ just (σ [ x := v ])

    b-assign-⊥ :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : State } →
        A⟦ aexp ⟧ σ ≡ exn →
    ----------------------------------------------------------
        [ assign x aexp , σ ]⇓ exn

    b-skip :
        { σ : State } →
    ----------------------------------------------------------
        [ skip , σ ]⇓ just σ

    b-seq :
        { stm1 stm2 : Stm} →
        { σ σ'' : State } →
        { σ'⊥ : Maybe State} →
        [ stm1 , σ ]⇓ just σ'' →
        [ stm2 , σ'' ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ seq stm1 stm2 , σ ]⇓ σ'⊥

    b-seq-⊥ :
        { stm1 stm2 : Stm} →
        { σ : State } →
        [ stm1 , σ ]⇓ exn →
    ----------------------------------------------------------
        [ seq stm1 stm2 , σ ]⇓ exn

    b-ite-tt :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        { σ'⊥ : Maybe State } →
        B⟦ b ⟧ σ ≡ just true →
        [ stm1 , σ ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⇓ σ'⊥

    b-ite-ff :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        { σ'⊥ : Maybe State } →
        B⟦ b ⟧ σ ≡ just false →
        [ stm2 , σ ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⇓ σ'⊥

    b-ite-⊥ :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ exn →
    ----------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⇓ exn

    b-whiledo-tt :
        { b : Bexp } →
        { stm : Stm } →
        { σ σ'' : State } →
        { σ'⊥ : Maybe State } →
        B⟦ b ⟧ σ ≡ just true →
        [ stm , σ ]⇓ just σ'' →
        [ whiledo b stm , σ'' ]⇓ σ'⊥ →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ σ'⊥

    b-whiledo-ff :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ just false →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ just σ

    b-whiledo-⊥₁ :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ exn →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ exn

    b-whiledo-⊥₂ :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ just true →
        [ stm , σ ]⇓ exn →
    ----------------------------------------------------------
        [ whiledo b stm , σ ]⇓ exn