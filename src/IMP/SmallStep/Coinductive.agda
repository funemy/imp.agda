{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This module extends our small-step semantics (i.e., IMP.SmallStep)
-- with coinductive infinite derivation sequences.
-- It is kept separate because coinductive definitions require the
-- `--guardedness` option, which can only be imported if the parent
-- module also turned on the same option, hence it's more convenient
-- to keep this separate.
module IMP.SmallStep.Coinductive where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Integer as I using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (z≤n)
open import Data.Product.Base using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤) renaming (tt to unit)
open import IMP.Base
open import IMP.Examples
open import IMP.Syntax
open import IMP.SmallStep.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary.Negation using (¬_)

-- This coinductive record **only** represent infinite derivation sequences
-- for small-step semantics.
--
-- Note that this definition only covers divergence, but not terminating executions.
record [_,_]⟶∞ (stm : Stm) (σ : State) : Set where
    coinductive
    constructor _::∞_
    field
        { stm' } : Stm
        { σ' } : State
        hd : [ stm , σ ]⟶ just (inj₂ (stm' , σ'))
        tl : [ stm' , σ' ]⟶∞

open [_,_]⟶∞ public

-- Showing skip definitely won't diverge (for arbitrary states)
-- This is done by pattern matching on the head of the infinite trace (i.e., `trace .hd`),
-- and clearly there's no way to construct such a single-step for assignments.
skip-nodiv : ∀ {σ : State} → ¬ [ skip , σ ]⟶∞
skip-nodiv trace with trace .hd
... | ()

-- The same proof as above, but for assignments.
assign-nodiv : {σ : State} {x : SSymbol} {aexp : Aexp} → ¬ [ assign x aexp , σ ]⟶∞
assign-nodiv trace with trace .hd
... | ()

-- Having an eseq implies there's no infinite derivation sequence, or
-- the statement is non-diverging.
~>*-implies-nodiv :
    { stm : Stm } { σ : State } { σ' : Maybe State } →
    [ stm , σ ]~>* σ' →
    ¬ [ stm , σ ]⟶∞
~>*-implies-nodiv (eseq-id (s-assign x)) t with t .hd
... | ()
~>*-implies-nodiv (eseq-id s-skip) t with t .hd
... | ()
~>*-implies-nodiv (eseq-id-⊥ (s-assign-⊥ step)) t with t .hd
... | ()
~>*-implies-nodiv (eseq-id-⊥ (s-seq-⊥ {stm1} {stm2} {σ} step)) t
    with [∙,∙]⟶∙-unique (t .hd) (s-seq-⊥ {stm2 = stm2} step)
... | ()
~>*-implies-nodiv (eseq-id-⊥ (s-ite-⊥ {b} {σ = σ} step)) t
    with [∙,∙]⟶∙-unique (t .hd) (s-ite-⊥ step)
... | ()
~>*-implies-nodiv (eseq-id-⊥ (s-while-⊥ step)) t with [∙,∙]⟶∙-unique (t .hd) (s-while-⊥ step)
... | ()
-- In the `eseq-cons` case, both our eseq and the infinite trace will have a single-step as head.
-- Due to local determinism (i.e., lemma `[∙,∙]⟶∙-unique`), the two steps must be identical.
-- Therefore, the tail of the eseq and the tail of `t` must starts at the same config.
-- By induction hypothesis, we know it is impossible for the starting config (of tail) to have an
-- infinite trace, hence contradicting the fact that we have the tail of `t`, i.e., `t .tl`.
~>*-implies-nodiv {stm} (eseq-cons x eseq) t with [∙,∙]⟶∙-unique (t .hd) x
... | refl =
    let subt = ~>*-implies-nodiv eseq in
    subt (t .tl)

-- An example that should diverge
whiletrue-div : (σ : State) → [ (WHILE tt DO skip) , σ ]⟶∞
whiletrue-div σ .stm' = skip ⨾ WHILE tt DO skip
whiletrue-div σ .σ' = σ
whiletrue-div σ .hd = s-while-tt refl
whiletrue-div σ .tl .stm' = WHILE tt DO skip
whiletrue-div σ .tl .σ' = σ
whiletrue-div σ .tl .hd = s-seq-2 s-skip
whiletrue-div σ .tl .tl = whiletrue-div σ

-- Lemma:
-- for a sequence `s1 ⨾ s2`, if `s1` diverges, then `s1 ⨾ s2` diverges.
s1∞-implies-s1⨾s2∞ :
    { s1 s2 : Stm } { σ : State } →
    [ s1 , σ ]⟶∞ →
    [ s1 ⨾ s2 , σ ]⟶∞
s1∞-implies-s1⨾s2∞ {s2 = s2} trace .stm' = trace .stm' ⨾ s2
s1∞-implies-s1⨾s2∞ trace .σ' = trace .σ'
s1∞-implies-s1⨾s2∞ trace .hd = s-seq-1 (trace .hd)
s1∞-implies-s1⨾s2∞ trace .tl = s1∞-implies-s1⨾s2∞ (trace .tl)

-- Lemma:
-- For a sequence `stm1 ⨾ stm2`, if `stm1` terminates normally (i.e., has a deseq),
-- then we can concatenate the deseq with a coinductive derivation sequence of stm2
-- to get a new coinductive sequence for the whole sequence.
--
-- This is needed for the lemma `nodiv-seq2` below
dseq1-concat-trace2 :
    { stm1 stm2 : Stm } { σ σ' : State } →
    [ stm1 , σ ]⟶* σ' →
    [ stm2 , σ' ]⟶∞ →
    [ stm1 ⨾ stm2 , σ ]⟶∞
dseq1-concat-trace2 (dseq-id step) trace2 = (s-seq-2 step) ::∞ trace2
dseq1-concat-trace2 (dseq-cons step dseq1) trace2 =
    (s-seq-1 step) ::∞ (dseq1-concat-trace2 dseq1 trace2)

-- Lemmas (properties of non-diverging seq):
nodiv-seq1 :
    { stm1 stm2 : Stm } { σ : State } →
    ¬ [ stm1 ⨾ stm2 , σ ]⟶∞ →
    ¬ [ stm1 , σ ]⟶∞
nodiv-seq1 ¬trace12 trace1 =
    let trace12 = s1∞-implies-s1⨾s2∞ trace1 in
    ¬trace12 trace12

nodiv-seq2 :
    { stm1 stm2 : Stm } { σ σ' : State } →
    ¬ [ stm1 ⨾ stm2 , σ ]⟶∞ →
    [ stm1 , σ ]~>* just σ' →
    ¬ [ stm2 , σ' ]⟶∞
nodiv-seq2 ¬trace12 eseq1 trace2 =
    let dseq1 = to-dseq eseq1 in
    ¬trace12 (dseq1-concat-trace2 dseq1 trace2)

-- Lemmas (properties of non-diverging if-then-else)
-- We split the lemma into two, where the predicate evaluates to ture/false.
-- The case where the predicate leads to exception is not needed, as in such cases,
-- the interpretation directly steps to exception without interpreting the sub-statements.
nodiv-ite-tt :
    { p : Bexp } { stm1 stm2 : Stm } { σ : State } →
    ¬ [ ite p stm1 stm2 , σ ]⟶∞ →
    B⟦ p ⟧ σ ≡ just true →
    ¬ [ stm1 , σ ]⟶∞
nodiv-ite-tt ¬trace eval trace1 = ¬trace (s-ite-tt eval ::∞ trace1)

nodiv-ite-ff :
    { p : Bexp } { stm1 stm2 : Stm } { σ : State } →
    ¬ [ ite p stm1 stm2 , σ ]⟶∞ →
    B⟦ p ⟧ σ ≡ just false →
    ¬ [ stm2 , σ ]⟶∞
nodiv-ite-ff ¬trace eval trace2 = ¬trace (s-ite-ff eval ::∞ trace2)

-- Lemma (non-diverging whildo/tt, non-diverging sub-statements):
nodiv-while/stm :
    { p : Bexp } { stm : Stm } { σ : State } →
    ¬ [ whiledo p stm , σ ]⟶∞ →
    B⟦ p ⟧ σ ≡ just true →
    ¬ [ stm , σ ]⟶∞
nodiv-while/stm ¬trace eval trace/stm = ¬trace (s-while-tt eval ::∞ s1∞-implies-s1⨾s2∞ trace/stm)

nodiv-while/unroll :
    { p : Bexp } { stm : Stm } { σ : State } →
    ¬ [ whiledo p stm , σ ]⟶∞ →
    B⟦ p ⟧ σ ≡ just true →
    ¬ [ stm ⨾ whiledo p stm , σ ]⟶∞
nodiv-while/unroll ¬trace eval trace/unroll =
    let ¬trace/stm = nodiv-while/stm ¬trace eval in
    ¬trace (s-while-tt eval ::∞ trace/unroll)

-- The first attempt to define a (partial) trace for loops
module loop-trace1 where
    record [WHILE_DO_,_]◯ (p : Bexp) (stm : Stm) (σ : State) : Set where
        coinductive
        constructor ⟨_⟩::_
        field
            { b } : Maybe Bool
            { σ' } : State
            pred : B⟦ p ⟧ σ ≡ b
            unroll : [ stm , σ ]~>* just σ'
            loop : [WHILE p DO stm , σ' ]◯

    open [WHILE_DO_,_]◯

    while-tt-skip : (σ : State) → [WHILE tt DO skip , σ ]◯
    while-tt-skip σ .b = just true
    while-tt-skip σ .σ' = σ
    while-tt-skip σ .pred = refl
    while-tt-skip σ .unroll = eseq-id s-skip
    while-tt-skip σ .loop = while-tt-skip σ

    while-t>0-t+1 :
        -- this construction requires a loop invariant
        (σ : State) → { v : I.ℤ } → (σ X ≡ just v) → (pf : (+ 0) I.≤ v) →
        [WHILE (N 0) ≤? `X DO (X ← plus `X (N 1)) , σ  ]◯
    while-t>0-t+1 _ _ _ .b = just true
    while-t>0-t+1 σ {v} _ _ .σ' = σ [ X := v I.+ (+ 1) ]
    while-t>0-t+1 _ v (I.+≤+ m≤n) .pred rewrite v = refl
    while-t>0-t+1 _ {v} veq _ .unroll =
        let pf = cong (λ x → vplus x (just (+ 1))) veq in
        eseq-id  (s-assign pf)
    while-t>0-t+1 σ {v} _ (I.+≤+ m≤n) .loop =
        while-t>0-t+1 (σ [ X := v I.+ (+ 1) ]) refl (I.+≤+ z≤n)

    -- This definition cannot encode terminating loops like below
    --
    -- while-ff-skip : (σ : State) → [WHILE ff DO skip , σ ]◯
    -- while-ff-skip σ .b = just false
    -- while-ff-skip σ .σ' = σ
    -- while-ff-skip σ .pred = refl
    -- while-ff-skip σ .unroll = eseq-id s-skip
    -- while-ff-skip σ .loop = {!   !}

mutual
    LoopNextState : Maybe Bool → Set
    LoopNextState (just true) = Maybe State
    LoopNextState (just false) = ⊤
    LoopNextState nothing = ⊤

    LoopUnroll : (b : Maybe Bool) → Stm → State → LoopNextState b → Set
    LoopUnroll (just true) stm σ σ' = [ stm , σ ]~>* σ'
    LoopUnroll _ _ _ _ = ⊤

    LoopNext : (b : Maybe Bool) → Bexp → Stm → LoopNextState b → Set
    LoopNext (just true) p stm (just σ) = [WHILE p DO stm , σ ]◯
    LoopNext (just true) p stm nothing = ⊤
    LoopNext _ _ _ _ = ⊤

    record [WHILE_DO_,_]◯ (p : Bexp) (stm : Stm) (σ : State) : Set where
        coinductive
        constructor ⟨_⟩::_
        field
            { b } : Maybe Bool
            pred : B⟦ p ⟧ σ ≡ b
            { σ' } : LoopNextState b
            unroll : LoopUnroll b stm σ σ'
            loop : LoopNext b p stm σ'

open [WHILE_DO_,_]◯ public

while-tt-skip : (σ : State) → [WHILE tt DO skip , σ ]◯
while-tt-skip σ .b = just true
while-tt-skip σ .pred = refl
while-tt-skip σ .σ' = just σ
while-tt-skip σ .unroll = eseq-id s-skip
while-tt-skip σ .loop = while-tt-skip σ

while-ff-skip : (σ : State) → [WHILE ff DO skip , σ ]◯
while-ff-skip σ .b = just false
while-ff-skip σ .pred = refl
while-ff-skip σ .σ' = unit
while-ff-skip σ .unroll = unit
while-ff-skip σ .loop = unit

-- eval/loop :
--     (p : Bexp) (stm : Stm) (σ : State) { σ₁ : Maybe State } → [ stm , σ ]~>* σ₁ →
--     [WHILE p DO stm , σ ]◯
-- eval/loop p stm σ unroll .b = B⟦ p ⟧ σ
-- eval/loop p stm σ unroll .pred = refl
-- eval/loop p stm σ {σ₁} unroll .σ' with B⟦ p ⟧ σ
-- ... | nothing = unit
-- ... | just false = unit
-- ... | just true = σ₁
-- eval/loop p stm σ unroll .unroll with B⟦ p ⟧ σ
-- ... | nothing = unit
-- ... | just false = unit
-- ... | just true = unroll
-- eval/loop p stm σ {σ₁} unroll .loop with B⟦ p ⟧ σ
-- ... | nothing = unit
-- ... | just false = unit
-- ... | just true with σ₁
-- ...     | nothing = unit
-- ...     | just σ₁ with B⟦ p ⟧ σ₁ in eq
-- ...         | nothing = (⟨ eq ⟩:: unit) unit
-- ...         | just false = (⟨ eq ⟩:: unit) unit
-- ...         | just true = (⟨ eq ⟩:: {!  !}) {!   !}

-- Lemma (non-diverging sequences implies eseq):
-- For any non-diverging computation, there exists a corresponding eseq
-- Proof by structural induction on statements.
nodiv-implies-[∙,∙]~>*∙ :
    ∀ { stm : Stm } { σ : State } →
    (¬ [ stm , σ ]⟶∞) → ∃[ σ' ] [ stm , σ ]~>* σ'
-- trivial, since assignment definitely terminate
nodiv-implies-[∙,∙]~>*∙ {assign x aexp} {σ} ¬trace with A⟦ aexp ⟧ σ in eq
... | just v = just (σ [ x := v ]) , eseq-id (s-assign eq)
... | nothing = exn , eseq-id-⊥ (s-assign-⊥ eq)
-- trivial, since skip definitely terminate
nodiv-implies-[∙,∙]~>*∙ {skip} ¬trace = just _ , eseq-id s-skip
-- Use lemma `nodiv-seq` to show that, when `stm1 ⨾ stm2` do not diverge, `stm1` is non-diverging.
-- Use inductive hypothesis, we know that `stm1` has an eseq.
-- Case split on the eseq of `stm1`
--   - If `stm1` steps to exception, then `stm1 ⨾ stm2` also steps to exception
--   - If `stm1` steps normally, then by lemma `nodiv-seq2`, `stm2` is also non-diverging.
--     By inductive hypotheses, we have eseq for both sub-statements, and we can use
--     `eseq∘` defined in `IMP.SmallStep` to compose them.
nodiv-implies-[∙,∙]~>*∙ {seq stm1 stm2} {σ} ¬trace with nodiv-implies-[∙,∙]~>*∙ (nodiv-seq1 ¬trace)
... | just σ' , eseq1 =
    let (σ'' , eseq2) = nodiv-implies-[∙,∙]~>*∙ (nodiv-seq2 ¬trace eseq1) in
    σ'' , eseq∘ eseq1 eseq2
... | nothing , eseq1 = exn , s1⊥-implies-s1⨾s2⊥ stm1 stm2 σ eseq1
nodiv-implies-[∙,∙]~>*∙ {ite p stm1 stm2} {σ} ¬trace with B⟦ p ⟧ σ in eq
... | just false =
    let ¬trace2 = nodiv-ite-ff ¬trace eq  in
    let (σ' , eseq2) = nodiv-implies-[∙,∙]~>*∙ ¬trace2 in
    σ' , eseq-cons (s-ite-ff eq) eseq2
... | just true =
    let ¬trace1 = nodiv-ite-tt ¬trace eq  in
    let (σ' , eseq1) = nodiv-implies-[∙,∙]~>*∙ ¬trace1 in
    σ' , eseq-cons (s-ite-tt eq) eseq1
... | nothing = exn , eseq-id-⊥ (s-ite-⊥ eq)
nodiv-implies-[∙,∙]~>*∙ {whiledo p stm} {σ} ¬trace with B⟦ p ⟧ σ in eq
... | nothing = exn , eseq-id-⊥ (s-while-⊥ eq)
... | just false = just σ , eseq-cons (s-while-ff eq) (eseq-id s-skip)
... | just true with nodiv-implies-[∙,∙]~>*∙ (nodiv-while/stm ¬trace eq)
...                | just σ , snd = {!   !} , {!   !}
...                | nothing , snd = exn , eseq-cons (s-while-tt eq) (s1⊥-implies-s1⨾s2⊥ stm (whiledo p stm) σ snd)

-- Lemma:
-- Programs in IMP is either terminating or non-terminating.
div-or-nodiv : ∀ (σ : State) (stm : Stm) → [ stm , σ ]⟶∞ ⊎ (¬ [ stm , σ ]⟶∞)
div-or-nodiv σ (assign x aexp) = inj₂ assign-nodiv
div-or-nodiv σ skip = inj₂ skip-nodiv
div-or-nodiv σ (seq stm1 stm2) with div-or-nodiv σ stm1
... | inj₁ trace =
    let hd = s-seq-1 (trace .hd) in
    let tl = s1∞-implies-s1⨾s2∞ (trace .tl) in
    inj₁ (hd ::∞ tl)
... | inj₂ ¬trace = {!   !}
div-or-nodiv σ (ite p stm1 stm2) with B⟦ p ⟧ σ in eq
... | just true = {!   !}
... | just false = {!   !}
div-or-nodiv σ (ite p stm1 stm2) | nothing =
    inj₂ (~>*-implies-nodiv (eseq-id-⊥ (s-ite-⊥ eq)))
div-or-nodiv σ (whiledo p stm) with B⟦ p ⟧ σ in eq
... | nothing = inj₂ ((~>*-implies-nodiv (eseq-id-⊥ (s-while-⊥ eq))))
... | just false =
    inj₂ (~>*-implies-nodiv (eseq-cons (s-while-ff eq) (eseq-id s-skip)))
... | just true = {!   !}