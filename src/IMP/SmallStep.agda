module IMP.SmallStep where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import IMP.Base
open import IMP.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation using (¬_)

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

-- Derivation sequence (finite), or dseq
-- Note that, by definition, this sequence cannot raise exceptions, because
-- the sequence is constructed backwards from the end, which is a single-step
-- into a well-formed state (instead of an exception).
infix 4 [_,_]⟶*_
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

-- A potentially exceptional derivation sequence (finite), or eseq
-- Comparing to the derivation sequence defined above (i.e., [∙,∙]⟶*∙),
-- the only difference is a new rule `eseq-id-⊥`.
-- The idea is that an exception have to be the _end_ of a sequence;
-- it is not allowed to prepend a single step into exception to another sequence.
infix 4 [_,_]~>*_
data [_,_]~>*_ : (stm : Stm) → (σ : State) → (σ' : Maybe State) → Set where
    eseq-id :
        { stm : Stm } →
        { σ σ' : State } →
        [ stm , σ ]⟶ just (inj₁ σ') →
    -----------------------------------------------------------------
        [ stm , σ ]~>* just σ'

    eseq-id-⊥ :
        { stm : Stm } →
        { σ : State } →
        [ stm , σ ]⟶ exn →
    -----------------------------------------------------------------
        [ stm , σ ]~>* exn

    eseq-cons :
        { stm stm' : Stm } →
        { σ σ'' : State } →
        { σ' : Maybe State } →
        [ stm , σ ]⟶ just (inj₂ (stm' , σ'' )) →
        [ stm' , σ'' ]~>* σ' →
    -----------------------------------------------------------------
        [ stm , σ ]~>* σ'

    -- NOTE: This rule is useful for lifting an exceptional evaluation of stm1 to
    -- a corresponding one of (stm1 ⨾ stm2).
    -- But this rule is admissible, as we proven below.
    -- eseq-↑-seq :
    --     { stm1 stm2 : Stm } →
    --     { σ : State } →
    --     [ stm1 , σ ]~>* exn →
    -- -----------------------------------------------------------------
    --     [ stm1 ⨾ stm2 , σ ]~>* exn

-- Lemma:
-- We show that the rule commented out above (i.e., eseq-↑-seq) is not necessary,
-- because it is admissible.
s1⊥-implies-s1⨾s2⊥ :
    ∀ (stm1 stm2 : Stm) (σ : State) →
    [ stm1 , σ ]~>* exn →
    [ stm1 ⨾ stm2 , σ ]~>* exn
s1⊥-implies-s1⨾s2⊥ stm1 stm2 σ (eseq-id-⊥ x) = eseq-id-⊥ (s-seq-⊥ x)
s1⊥-implies-s1⨾s2⊥ stm1 stm2 σ (eseq-cons {stm' = stm'} {σ'' = σ''} step eseq) =
    let eseq' = s1⊥-implies-s1⨾s2⊥ stm' stm2 σ'' eseq in
    eseq-cons (s-seq-1 step) eseq'

-- Lemma:
-- We show that for every statement, there's only one possible result for small-step evaluation.
-- The proof looks long, but it's actually trivial.
-- The general idea is to simultaneously do induction on both small-step derivations and unify all
-- the equalities, the proof will then resolve to either `refl` or absurdity.
[∙,∙]⟶∙-unique :
    ∀ (stm : Stm) {σ : State} {c1 c2 : Maybe Config}→
    [ stm , σ ]⟶ c1 →
    [ stm , σ ]⟶ c2 →
    c1 ≡ c2
[∙,∙]⟶∙-unique (assign x aexp) (s-assign A⟦aexp⟧σ1) (s-assign A⟦aexp⟧σ2)
    rewrite A⟦aexp⟧σ1
    rewrite A⟦aexp⟧σ2
    = refl
[∙,∙]⟶∙-unique (assign x aexp) (s-assign A⟦aexp⟧σ) (s-assign-⊥ A⟦aexp⟧σ⊥)
    -- A⟦aexp⟧σ shows that aexp evaluates to some value v (as equality),
    -- hence A⟦aexp⟧σ⊥ will resolve to `just _ ≡ nothing` after the rewrite.
    rewrite A⟦aexp⟧σ
    -- By pattern matching on this equality, it's evident that this is absurdity.
    with A⟦aexp⟧σ⊥
... | ()
[∙,∙]⟶∙-unique (assign x aexp) (s-assign-⊥ A⟦aexp⟧σ⊥) (s-assign A⟦aexp⟧σ)
    -- This is the symmetrical case of what's above
    rewrite A⟦aexp⟧σ
    with A⟦aexp⟧σ⊥
... | ()
[∙,∙]⟶∙-unique (assign x aexp) (s-assign-⊥ A⟦aexp⟧σ⊥1) (s-assign-⊥ A⟦aexp⟧σ⊥2) = refl
[∙,∙]⟶∙-unique skip s-skip s-skip = refl
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-1 step1) (s-seq-1 step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | refl = refl
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-1 step1) (s-seq-2 step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | ()
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-1 step1) (s-seq-⊥ step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | ()
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-2 step1) (s-seq-1 step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | ()
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-2 step1) (s-seq-2 step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | refl = refl
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-2 step1) (s-seq-⊥ step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | ()
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-⊥ step1) (s-seq-1 step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | ()
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-⊥ step1) (s-seq-2 step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | ()
[∙,∙]⟶∙-unique (seq stm1 stm2) (s-seq-⊥ step1) (s-seq-⊥ step2)
    with [∙,∙]⟶∙-unique stm1 step1 step2
... | refl = refl
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-tt p/tt1) (s-ite-tt p/tt2) = refl
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-tt p/tt) (s-ite-ff p/ff)
    rewrite p/tt
    with p/ff
... | ()
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-tt p/tt) (s-ite-⊥ p/⊥)
    rewrite p/tt
    with p/⊥
... | ()
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-ff p/ff) (s-ite-tt p/tt)
    rewrite p/tt
    with p/ff
... | ()
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-ff p/ff1) (s-ite-ff p/ff2)
    rewrite p/ff1
    with p/ff2
... | refl = refl
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-ff p/ff) (s-ite-⊥ p/⊥)
    rewrite p/ff
    with p/⊥
... | ()
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-⊥ p/⊥) (s-ite-tt p/tt)
    rewrite p/⊥
    with p/tt
... | ()
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-⊥ p/⊥) (s-ite-ff p/ff)
    rewrite p/⊥
    with p/ff
... | ()
[∙,∙]⟶∙-unique (ite p stm1 stm2) (s-ite-⊥ p/⊥1) (s-ite-⊥ p/⊥2) rewrite p/⊥1 = refl
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-tt p/tt1) (s-while-tt p/tt2) rewrite p/tt1 = refl
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-tt p/tt) (s-while-ff p/ff)
    rewrite p/tt
    with p/ff
... | ()
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-tt p/tt) (s-while-⊥ p/⊥)
    rewrite p/tt
    with p/⊥
... | ()
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-ff p/ff) (s-while-tt p/tt)
    rewrite p/ff
    with p/tt
... | ()
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-ff p/ff1) (s-while-ff p/ff2) rewrite p/ff1 = refl
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-ff p/ff) (s-while-⊥ p/⊥)
    rewrite p/ff
    with p/⊥
... | ()
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-⊥ p/⊥) (s-while-tt p/tt)
    rewrite p/⊥
    with p/tt
... | ()
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-⊥ p/⊥) (s-while-ff p/ff)
    rewrite p/⊥
    with p/ff
... | ()
[∙,∙]⟶∙-unique (whiledo p stm) (s-while-⊥ p/⊥1) (s-while-⊥ p/⊥2) rewrite p/⊥1 = refl

-- Lemma:
-- We show that our previous definition of derivation sequences
-- cannot represent exceptional executions.
--
-- This lemma can be seen as a special case of showing that the evaluation defined is deterministic.
dseq-no-exn :
    ∀ (stm : Stm) {σ σ' : State} →
    [ stm , σ ]⟶* σ' → ¬([ stm , σ ]~>* exn)
dseq-no-exn stm (dseq-id step) (eseq-id-⊥ step⊥)
    with [∙,∙]⟶∙-unique stm step step⊥
... | ()
dseq-no-exn stm (dseq-cons step dseq) (eseq-id-⊥ step⊥)
    with [∙,∙]⟶∙-unique stm step step⊥
... | ()
dseq-no-exn stm (dseq-id step1) (eseq-cons step2 eseq⊥)
    with [∙,∙]⟶∙-unique stm step1 step2
... | ()
-- We proof this case by:
-- 1. `step1` and `step2` are two single-steps from the same statement, hence they must step into the same
--    result, by the lemma [∙,∙]⟶∙-unique proven above.
-- 2. As a result, the tails of both sequences will start at the same statement and state, hence by
--    inductive hypothesis, the proof goes through.
dseq-no-exn stm (dseq-cons step1 dseq) (eseq-cons step2 eseq⊥)
    with [∙,∙]⟶∙-unique stm step1 step2
-- the omitted argument is the statement produced by the first step
... | refl = dseq-no-exn _ dseq eseq⊥

-- WIP: infinite derivation sequence
-- record [_,_]⟶_ (stm : Stm) (σᵢ : State) (σ : State) : Set where
--     coinductive
--     field
--         trace :