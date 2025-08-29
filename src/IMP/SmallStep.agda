module IMP.SmallStep where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just)
open import Data.Product as P using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Config : Set
Config = State ⊎ (Stm × State)

-- small-step semantics
-- The small-step semantics can either step into a new state for statements
-- like assign or skip, or step into a pair of next statement and a new state.
-- This is defined as the type `Config` above, additionally, we wrap it in `Maybe`
-- to model exceptions due to state-lookup.
data [_,_]⟶_ : (stm : Stm) → (σ : State) → (γ : Maybe Config) → Set where
    s-assign :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : State } →
        { v : Value } →
        A⟦ aexp ⟧ σ ≡ just v →
    -----------------------------------------------------------------
        [ assign x aexp , σ ]⟶ just (inj₁ (σ [ x := v ]))

    s-assign-⊥ :
        { x : SSymbol } →
        { aexp : Aexp } →
        { σ : State } →
        { v : Value } →
        A⟦ aexp ⟧ σ ≡ exn →
    -----------------------------------------------------------------
        [ assign x aexp , σ ]⟶ exn

    s-skip :
        { σ : State } →
    -----------------------------------------------------------------
        [ skip , σ ]⟶ just (inj₁ σ)

    s-seq-1 :
        { stm1 stm2 stm1' : Stm } →
        { σ σ' : State } →
        [ stm1 , σ ]⟶ just (inj₂ (stm1' , σ' )) →
    -----------------------------------------------------------------
        [ seq stm1 stm2 , σ ]⟶ just (inj₂ (seq stm1' stm2 , σ'))

    s-seq-2 :
        { stm1 stm2 : Stm } →
        { σ σ' : State } →
        [ stm1 , σ ]⟶ just (inj₁ σ') →
    -----------------------------------------------------------------
        [ seq stm1 stm2 , σ ]⟶ just (inj₂ ( stm2 , σ' ))

    s-seq-⊥ :
        { stm1 stm2 : Stm } →
        { σ : State } →
        [ stm1 , σ ]⟶ exn →
    -----------------------------------------------------------------
        [ seq stm1 stm2 , σ ]⟶ exn

    s-ite-tt :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ just true →
    -----------------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⟶ just (inj₂ (stm1 , σ))

    s-ite-ff :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ just false →
    -----------------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⟶ just (inj₂ (stm2 , σ))

    s-ite-⊥ :
        { b : Bexp } →
        { stm1 stm2 : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ exn →
    -----------------------------------------------------------------
        [ ite b stm1 stm2 , σ ]⟶ exn

    s-while-tt :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ just true →
    ---------------------------------------------------------------------
        [ whiledo b stm , σ ]⟶ just (inj₂ (seq stm (whiledo b stm) , σ))

    s-while-ff :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ just false →
    ---------------------------------------------------------------------
        [ whiledo b stm , σ ]⟶ just (inj₂ (skip , σ))

    s-while-⊥ :
        { b : Bexp } →
        { stm : Stm } →
        { σ : State } →
        B⟦ b ⟧ σ ≡ exn →
    -----------------------------------------------------------------
        [ whiledo b stm , σ ]⟶ exn

-- derivation sequence (finite)
-- Note that, by definition, this sequence cannot raise exceptions, because
-- the sequence is constructed backwards from the end, which is a single-step
-- into a well-formed state (instead of an exception).
data [_,_]⟶*_ : (stm : Stm) → (σ : State) → (σ' : State) → Set where
    dseq-id :
        { stm : Stm } →
        { σ σ' : State } →
        [ stm , σ ]⟶ just (inj₁ σ') →
    -----------------------------------------------------------------
        [ stm , σ ]⟶* σ'

    dseq-cons :
        { stm stm' : Stm } →
        { σ σ' σ'' : State } →
        [ stm , σ ]⟶ just (inj₂ (stm' , σ'' )) →
        [ stm' , σ'' ]⟶* σ' →
    -----------------------------------------------------------------
        [ stm , σ ]⟶* σ'

-- some sugar for composing the derivation sequence
infixr -20 _::⟶⟨_⟩_
_::⟶⟨_⟩_ :
    { stm stm' : Stm } →
    ( σ : State ) →
    { σ'' σ' : State } →
    ( step : [ stm , σ ]⟶ just (inj₂ (stm' , σ'' )) ) →
    ( rest : [ stm' , σ'' ]⟶* σ' ) →
    [ stm , σ ]⟶* σ'
(_::⟶⟨_⟩_) {stm} σ {σ''} {σ'} step rest = dseq-cons step rest

dseq-id-syntax :
    { stm : Stm } →
    ( σ : State ) →
    ( σ' : State ) →
    ( step : [ stm , σ ]⟶ just (inj₁ σ') ) →
    [ stm , σ ]⟶* σ'
dseq-id-syntax {stm} σ σ' step = dseq-id step

infix -19 dseq-id-syntax
syntax dseq-id-syntax σ σ' step = σ ::⟶⟨ step ⟩∎ σ'

-- composing two derivation sequences
dseq∘ :
    { stm1 stm2 : Stm } →
    { σ σ' σ'' : State } →
    (deriv1 : [ stm1 , σ ]⟶* σ') →
    (deriv2 : [ stm2 , σ' ]⟶* σ'') →
    [ stm1 ⨾ stm2 , σ ]⟶* σ''
dseq∘ (dseq-id step) deriv2 = dseq-cons (s-seq-2 step) deriv2
dseq∘ (dseq-cons step deriv1) deriv2 =
    let tail = dseq∘ deriv1 deriv2 in
    dseq-cons (s-seq-1 step) tail

-- WIP: infinite derivation sequence
-- record [_,_]⟶_ (stm : Stm) (σᵢ : State) (σ : State) : Set where
--     coinductive
--     field
--         trace :