{-# OPTIONS --guardedness #-}

module IMP.SmallStep.Experiment2 where

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
        constructor mkT
        field
            unpack : ∃[ σ' ] ([ stm , σ ]⟶ σ' × ~>∞Tail σ')


open [_,_]~>∞ public

`hd : { stm : Stm } { σ : State } → [ stm , σ ]~>∞ → ∃[ σ' ] [ stm , σ ]⟶ σ'
`hd trace =
    let t =  trace .unpack in
    proj₁ t , proj₁ (proj₂ t)

`tl : { stm : Stm } { σ : State } → [ stm , σ ]~>∞ → ∃[ σ' ] ~>∞Tail σ'
`tl trace =
    let t =  trace .unpack in
    proj₁ t , proj₂ (proj₂ t)

-- Did I do something wrong here?
{-# TERMINATING #-}
eval∞ : (stm : Stm) → (σ : State) → [ stm , σ ]~>∞
eval∞ (assign x aexp) σ .unpack with A⟦ aexp ⟧ σ in eq
... | just v = just (inj₁ (σ [ x := v ])) , (s-assign eq , unit)
... | nothing = exn , s-assign-⊥ eq , unit
eval∞ skip σ .unpack = just (inj₁ σ) , (s-skip , unit)
eval∞ (seq stm1 stm2) σ .unpack with eval∞ stm1 σ .unpack
... | just (inj₁ σ') , step , unit =
    just (inj₂ ( stm2 , σ')) , s-seq-2 step , eval∞ stm2 σ'
... | just (inj₂ (stm1' , σ')) , step , snd =
    let stm' = stm1' ⨾ stm2 in
    just (inj₂ (stm' , σ')) , s-seq-1 step , eval∞ stm' σ' -- larger size
... | nothing , fst , unit = exn , s-seq-⊥ fst , unit
eval∞ (ite p stm1 stm2) σ .unpack with B⟦ p ⟧ σ in eq
... | nothing = exn , s-ite-⊥ eq , unit
... | just false = just (inj₂ (stm2 , σ)) , s-ite-ff eq , eval∞ stm2 σ
... | just true = just (inj₂ (stm1 , σ)) , s-ite-tt eq , eval∞ stm1 σ
eval∞ (whiledo p stm) σ .unpack with B⟦ p ⟧ σ in eq
... | nothing = exn , s-while-⊥ eq , unit
... | just false = just (inj₂ (skip , σ)) , s-while-ff eq , eval∞ skip σ
... | just true =
    let unroll = (stm ⨾ whiledo p stm) in
    just (inj₂ (unroll , σ)) , s-while-tt eq , eval∞ unroll σ -- larger size

example1 : Stm
example1 =
    WHILE tt DO skip ⨾
    WHILE tt DO skip

eval1 : [ example1 , σ₀ ]~>∞
eval1 = eval∞ example1 σ₀

-- _ : [ (skip ⨾ whiledo tt skip) ⨾ WHILE tt DO skip , σ₀ ]⟶
--   eval1 .tl .tl .tl .tl .tl .tl .tl .σ'
-- _ = eval1 .tl .tl .tl .tl .tl .tl .tl .hd

-- _ : eval1 .tl .tl .tl .tl .tl .tl .tl .σ' ≡ just (inj₂ ((whiledo tt skip ⨾ WHILE tt DO skip) , σ₀))
-- _ = refl

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

-- _ : eval2 .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl .tl ≡ unit
-- _ = refl

-- Lemma (all loops are described by eval∞)
allloops :
    { p : Bexp } { σ : State } { stm : Stm } →
    [ WHILE p DO stm , σ ]~>∞ →
    ∃[ σ' ] [ WHILE p DO stm , σ ]~>* σ' ⊎ [ WHILE p DO stm , σ ]⟶∞
allloops = {!   !}