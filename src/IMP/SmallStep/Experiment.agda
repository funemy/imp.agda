{-# OPTIONS --guardedness #-}

module IMP.SmallStep.Experiment where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product.Base using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤) renaming (tt to unit)
open import IMP.Base
open import IMP.Examples
open import IMP.Syntax
open import IMP.SmallStep.Base
open import IMP.SmallStep.Coinductive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

mutual
    ~>∞Tail : Maybe Config → Set
    ~>∞Tail (just (inj₁ σ)) = ⊤
    ~>∞Tail (just (inj₂ (stm' , σ'))) = [ stm' , σ' ]~>∞
    ~>∞Tail nothing = ⊤

    -- This is a coinductive definition for all possible small-step interpretation,
    -- including both terminating and non-terminating sequences.
    record [_,_]~>∞ (stm : Stm) (σ : State) : Set where
        coinductive
        constructor _::~_
        field
            { σ' } : Maybe Config
            hd : [ stm , σ ]⟶ σ'
            tl : ~>∞Tail σ'

open [_,_]~>∞ public

-- Did I do something wrong here?
{-# TERMINATING #-}
eval∞ : (stm : Stm) → (σ : State) → [ stm , σ ]~>∞
eval∞ (assign x aexp) σ .σ' with A⟦ aexp ⟧ σ
... | just v = just (inj₁ (σ [ x := v ]))
... | nothing = exn
eval∞ (assign x aexp) σ .hd with A⟦ aexp ⟧ σ in eq
... | just v = s-assign eq
... | nothing = s-assign-⊥ eq
eval∞ (assign x aexp) σ .tl with A⟦ aexp ⟧ σ
... | just v = unit
... | nothing = unit

eval∞ skip σ .σ' = just (inj₁ σ)
eval∞ skip σ .hd = s-skip
eval∞ skip σ .tl = unit

eval∞ (seq stm1 stm2) σ .σ' with eval∞ stm1 σ .σ'
... | just (inj₁ σ') = just (inj₂ (stm2 , σ'))
... | just (inj₂ (stm1' , σ')) = just (inj₂ ((stm1' ⨾ stm2) , σ'))
... | nothing = exn
eval∞ (seq stm1 stm2) σ .hd with eval∞ stm1 σ .σ' with eval∞ stm1 σ .hd
... | just (inj₁ σ') | step = s-seq-2 step
... | just (inj₂ (stm1' , σ')) | step = s-seq-1 step
... | nothing | step = s-seq-⊥ step
eval∞ (seq stm1 stm2) σ .tl with eval∞ stm1 σ .σ' with eval∞ stm1 σ .hd
... | just (inj₁ σ') | step = eval∞ stm2 σ'
... | just (inj₂ (stm1' , σ')) | step = eval∞ (stm1' ⨾ stm2) σ'
... | nothing | step = unit

eval∞ (ite p stm1 stm2) σ .σ' with B⟦ p ⟧ σ
... | just true = just (inj₂ (stm1 , σ))
... | just false = just (inj₂ (stm2 , σ))
... | nothing = exn
eval∞ (ite p stm1 stm2) σ .hd with B⟦ p ⟧ σ in eq
... | just true = s-ite-tt eq
... | just false = s-ite-ff eq
... | nothing = s-ite-⊥ eq
eval∞ (ite p stm1 stm2) σ .tl with B⟦ p ⟧ σ
... | just true = eval∞ stm1 σ
... | just false = eval∞ stm2 σ
... | nothing = unit

eval∞ (whiledo p stm) σ .σ' with B⟦ p ⟧ σ
... | just false = just (inj₂ (skip , σ))
... | just true = just (inj₂ ((stm ⨾ whiledo p stm) , σ))
... | nothing = exn
eval∞ (whiledo p stm) σ .hd with B⟦ p ⟧ σ in eq
... | just false = s-while-ff eq
... | just true = s-while-tt eq
... | nothing = s-while-⊥ eq
eval∞ (whiledo p stm) σ .tl with B⟦ p ⟧ σ in eq
... | just false = eval∞ skip σ
... | just true = eval∞ (stm ⨾ whiledo p stm) σ
... | nothing = unit

example1 : Stm
example1 =
    WHILE tt DO skip ⨾
    WHILE tt DO skip

eval1 : [ example1 , σ₀ ]~>∞
eval1 = eval∞ example1 σ₀

_ : [ (skip ⨾ whiledo tt skip) ⨾ WHILE tt DO skip , σ₀ ]⟶
  eval1 .tl .tl .tl .tl .tl .tl .tl .σ'
_ = eval1 .tl .tl .tl .tl .tl .tl .tl .hd

_ : eval1 .tl .tl .tl .tl .tl .tl .tl .σ' ≡ just (inj₂ ((whiledo tt skip ⨾ WHILE tt DO skip) , σ₀))
_ = refl

example2 : Stm
example2 =
    X ← (N 0) ⨾
    WHILE `X ≤? (N 3) DO
    (
        X ← plus (N 2) `X ⨾
        X ← sub `X (N 1)
    )

eval2 : [ example2 , σ₀ ]~>∞
eval2 = eval∞ example2 σ₀

_ : eval2 .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl ≡ unit
_ = refl

-- Lemma (all loops are described by eval∞)
allloops :
    { p : Bexp } { σ : State } { stm : Stm } →
    [ WHILE p DO stm , σ ]~>∞ →
    ∃[ σ' ] [ WHILE p DO stm , σ ]~>* σ' ⊎ [ WHILE p DO stm , σ ]⟶∞
allloops {p} {σ} trace with B⟦ p ⟧ σ in eq
... | nothing = inj₁ (exn , eseq-id-⊥ (s-while-⊥ eq))
... | just false = inj₁ (just σ , eseq-cons (s-while-ff eq) (eseq-id s-skip))
... | just true with eq with trace .σ' with trace .hd
allloops {p} {σ} trace | just true | p/tt | nothing | s-while-⊥ x
    rewrite p/tt
    with x
... | ()
allloops {p} {σ} trace | just true | p/tt | just (inj₂ _) | s-while-ff x
    rewrite p/tt
    with x
... | ()
allloops {p} {σ} trace | just true | p/tt | just (inj₂ (fst , snd)) | s-while-tt x
    with trace .tl
... | r = {!  !}