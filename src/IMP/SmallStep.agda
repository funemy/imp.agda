module IMP.SmallStep where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just)
open import Data.Product as P using (_×_)
open import Data.Sum as S using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

StepRes : Set
StepRes = State ⊎ (Stm × State)

-- small-step semantics
-- The small-step semantics can either step into a new state for statements
-- like assign or skip, or step into a pair of next statement and a new state.
-- This is defined as the type `StepRes` above, additionally, we wrap it in `Maybe`
-- to model exceptions due to state-lookup.
data [_,_]⟶_ : (stm : Stm) → (σ : State) → (γ : Maybe StepRes) → Set where
    s-assign :
        { x : SSymbol } →
        { aexp : Aexp } →
        { s : State } →
        { v : Value } →
        A⟦ aexp ⟧ s ≡ just v →
    -----------------------------------------------------------------
        [ assign x aexp , s ]⟶ just (inj₁ (s [ x := v ]))

    s-assign-⊥ :
        { x : SSymbol } →
        { aexp : Aexp } →
        { s : State } →
        { v : Value } →
        A⟦ aexp ⟧ s ≡ exn →
    -----------------------------------------------------------------
        [ assign x aexp , s ]⟶ exn

    s-skip :
        { s : State } →
    -----------------------------------------------------------------
        [ skip , s ]⟶ just (inj₁ s)

    s-seq-1 :
        { s1 s2 s1' : Stm } →
        { s s' : State } →
        [ s1 , s ]⟶ just (inj₂ (s1' , s' )) →
    -----------------------------------------------------------------
        [ seq s1 s2 , s ]⟶ just (inj₂ (seq s1' s2 , s'))

    s-seq-2 :
        { s1 s2 : Stm } →
        { s s' : State } →
        [ s1 , s ]⟶ just (inj₁ s') →
    -----------------------------------------------------------------
        [ seq s1 s2 , s ]⟶ just (inj₂ ( s2 , s' ))

    s-seq-⊥ :
        { s1 s2 : Stm } →
        { s : State } →
        [ s1 , s ]⟶ exn →
    -----------------------------------------------------------------
        [ seq s1 s2 , s ]⟶ exn

    s-ite-tt :
        { b : Bexp } →
        { s1 s2 : Stm } →
        { s : State } →
        B⟦ b ⟧ s ≡ just true →
    -----------------------------------------------------------------
        [ ite b s1 s2 , s ]⟶ just (inj₂ (s1 , s))

    s-ite-ff :
        { b : Bexp } →
        { s1 s2 : Stm } →
        { s : State } →
        B⟦ b ⟧ s ≡ just false →
    -----------------------------------------------------------------
        [ ite b s1 s2 , s ]⟶ just (inj₂ (s2 , s))

    s-ite-⊥ :
        { b : Bexp } →
        { s1 s2 : Stm } →
        { s : State } →
        B⟦ b ⟧ s ≡ exn →
    -----------------------------------------------------------------
        [ ite b s1 s2 , s ]⟶ exn

    s-while-tt :
        { b : Bexp } →
        { stm : Stm } →
        { s : State } →
        B⟦ b ⟧ s ≡ just true →
    ---------------------------------------------------------------------
        [ whiledo b stm , s ]⟶ just (inj₂ (seq stm (whiledo b stm) , s))

    s-while-ff :
        { b : Bexp } →
        { stm : Stm } →
        { s : State } →
        B⟦ b ⟧ s ≡ just false →
    ---------------------------------------------------------------------
        [ whiledo b stm , s ]⟶ just (inj₂ (skip , s))

    s-while-⊥ :
        { b : Bexp } →
        { stm : Stm } →
        { s : State } →
        B⟦ b ⟧ s ≡ exn →
    -----------------------------------------------------------------
        [ whiledo b stm , s ]⟶ exn

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

helper-dseq-id :
    { stm : Stm } →
    ( σ : State ) →
    ( σ' : State ) →
    ( step : [ stm , σ ]⟶ just (inj₁ σ') ) →
    [ stm , σ ]⟶* σ'
helper-dseq-id {stm} σ σ' step = dseq-id step

infix -19 helper-dseq-id
syntax helper-dseq-id σ σ' step = σ ::⟶⟨ step ⟩∎ σ'

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