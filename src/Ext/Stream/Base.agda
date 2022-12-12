{-# OPTIONS --guardedness #-}

module Ext.Stream.Base where

open import Data.Nat using (ℕ; zero; suc; _<_)
import Data.Nat.Properties as ℕ

-- infinite sequence
record Stream (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    hd : A
    tl : Stream A

open Stream

-- take the n-th element of as
take : {A : Set} (n : ℕ) (as : Stream A) → A
take zero as = hd as
take (suc n) as = take n (tl as)

-- function to stream
f→S : {A : Set} (f : (n : ℕ) → A) → Stream A
hd (f→S f) = f zero
tl (f→S f) = f→S (λ n → f (suc n))

const : {A B : Set} (a : A) → B → A
const a = λ _ → a

repeat : {A : Set} (a : A) → Stream A
repeat a = f→S (const a)

zipWith : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
zipWith {A} {B} {C} f as bs =  cs where
  cs : Stream C
  hd cs = f (hd as) (hd bs)
  tl cs = zipWith f (tl as) (tl bs)
  
-- picker is a map to subsequence
record Picker : Set where
  constructor _,_
  field
    f : ℕ → ℕ
    isMono : ∀ (n : ℕ) → f n < f (suc n)

-- construct a subsequence by a picker
sub : {A : Set} (pick : Picker) → Stream A → Stream A
sub (f , _) x = f→S (λ n → take (f n) x)

-- the same as tl
picker-tl : Picker
Picker.f picker-tl x = suc x
Picker.isMono picker-tl n = Data.Nat.s≤s ℕ.≤-refl
