{-# OPTIONS --guardedness #-}

module IMP.SmallStep.Experiment3 where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product.Base using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤) renaming (tt to unit)
open import IMP.Base
open import IMP.Examples
open import IMP.Syntax
open import IMP.SmallStep.NoExn
open import IMP.SmallStep.Coinductive
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- This is a coinductive definition for all possible small-step interpretation,
-- including both terminating and non-terminating sequences.
record [_,_]~>∞ (stm : Stm) (σ : State) : Set where
    coinductive
    field
        unpack : ∃[ stm' ] ∃[ σ' ] ([ stm , σ ]⟶ (stm' , σ') × [ stm' , σ' ]~>∞)

open [_,_]~>∞ public

_`stm' :
    { stm : Stm } { σ : State } →
    (t : [ stm , σ ]~>∞) →
    Stm
trace `stm' = trace .unpack .proj₁

_`σ' :
    { stm : Stm } { σ : State } →
    (t : [ stm , σ ]~>∞) →
    State
trace `σ' = trace .unpack .proj₂ .proj₁


_`hd :
    { stm : Stm } { σ : State } →
    (t : [ stm , σ ]~>∞) →
    [ stm , σ ]⟶ (t .unpack .proj₁ , t .unpack .proj₂ .proj₁)
trace `hd = trace .unpack .proj₂ .proj₂ .proj₁

_`tl :
    { stm : Stm } { σ : State } →
    (t : [ stm , σ ]~>∞) →
    [ t .unpack .proj₁ , t .unpack .proj₂ .proj₁ ]~>∞
trace `tl  = trace .unpack .proj₂ .proj₂ .proj₂

repeat/skip : (σ : State) → [ skip , σ ]~>∞
repeat/skip σ .unpack = skip , σ , s-skip , repeat/skip σ

{-# TERMINATING #-}
eval∞ : (stm : Stm) → (σ : State) → [ stm , σ ]~>∞
eval∞ (assign x aexp) σ .unpack =
    let σ' = σ [ x := A⌊ aexp ⌋ σ ] in
    skip , σ' , s-assign refl , repeat/skip σ'
eval∞ skip σ .unpack = skip , σ , s-skip , repeat/skip σ
eval∞ (seq stm1 stm2) σ .unpack with eval∞ stm1 σ .unpack
... | skip , σ' , step , tl = stm2 , (σ' , s-seq-2 step , eval∞ stm2 σ')
... | stm' , σ' , step , tl =
    let stm'' = (stm' ⨾ stm2) in
    stm'' , (σ' , s-seq-1 step , eval∞ stm'' σ') -- !!larger term
eval∞ (ite p stm1 stm2) σ .unpack with B⌊ p ⌋ σ in eq
... | true = stm1 , σ , s-ite-tt eq , eval∞ stm1 σ
... | false = stm2 , σ , s-ite-ff eq , eval∞ stm2 σ
eval∞ (whiledo p stm) σ .unpack with B⌊ p ⌋ σ in eq
... | true =
    let stm' = stm ⨾ whiledo p stm in
    stm' , σ , s-while-tt eq , eval∞ stm' σ -- !!larger term
... | false = skip , σ , s-while-ff eq , repeat/skip σ

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

-- _ : eval2 `tl `tl `tl `tl `tl `tl `tl `tl `tl `tl `tl `tl `tl `σ' ≡ ?
-- _ = refl