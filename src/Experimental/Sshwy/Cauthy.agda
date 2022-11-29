{-# OPTIONS --guardedness #-}

module Cauthy where

open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ⁿ_)
open import Data.Nat.Properties as ℕ

open import Data.Rational using (ℚ; 0ℚ; _<_; _-_; ∣_∣; Positive)
open import Data.Rational.Properties as ℚ
  using (+-inverseʳ; positive⁻¹)

open import Data.Product using (∃; Σ; Σ-syntax; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

-- import Data.Integer.Base as ℤ -- for better agda-mode output
-- open ℚ renaming (numerator to ↥_; denominator to ↧_)

open import Stream
  using (Stream; Picker; sub; take; repeat; const)
open import Stream.Properties using (f=S; sub-take; n≤mono; aᵢ<aᵢ₊₁⇒mono<)
open Stream.Stream

-- define cauthy convergence
data ε-N-Converge {ε : ℚ} (ε-pos : Positive ε) (N : ℕ) (x : Stream ℚ) : Set
  where
  ε-n-converge : 
    (∀ (n m : ℕ) 
      → N <ⁿ n 
      → N <ⁿ m 
      -------------------------
      → ∣ take m x - take n x ∣ < ε) 
    → ε-N-Converge {ε} ε-pos N x

-- converge under ε
data ε-Converge {ε : ℚ} (ε-pos : Positive ε) (x : Stream ℚ) : Set where
  ε-converge : Σ[ N ∈ ℕ ] ε-N-Converge {ε} ε-pos N x
               -------------------------------------
               → ε-Converge {ε} ε-pos x

-- define cauthy sequence
data Cauthy (x : Stream ℚ) : Set where
  cauthy : 
    (∀ {ε : ℚ} (ε-pos : Positive ε) → ε-Converge {ε} ε-pos x)
     → Cauthy x

≡⇒0 : {x y : ℚ} → x ≡ y → x - y ≡ 0ℚ
≡⇒0 {x} {y} x=y = trans (cong (_- y) x=y) (+-inverseʳ y)

ℚ-Converge : {ε : ℚ} (ε-pos : Positive ε) (x : ℚ)
  → ε-N-Converge {ε} ε-pos zero (repeat x)
ℚ-Converge {ε} ε-pos x = ε-n-converge prop where
  open ℚ.≤-Reasoning
  prop : (n m : ℕ)
    → zero <ⁿ n
    → zero <ⁿ m
    ---------------
    → ∣ take m (repeat x) - take n (repeat x) ∣ < ε
  prop n m N<n N<m =
    begin-strict
      ∣ xₘ - xₙ ∣
    ≡⟨ cong ∣_∣ (≡⇒0 (begin-equality
                       xₘ ≡⟨ f=S (const x) m ⟩
                       x  ≡˘⟨ f=S (const x) n ⟩
                       xₙ ∎)) ⟩
      0ℚ
    <⟨ positive⁻¹ ε-pos ⟩
      ε
    ∎
    where
    xₘ = take m (repeat x)
    xₙ = take n (repeat x) 

-- define cauthy sequence converging to ℚ
ℚ-Cauthy : (x : ℚ) → Cauthy (repeat x)
ℚ-Cauthy x = cauthy (λ ε-pos → ε-converge (zero , ℚ-Converge ε-pos x))

getN : {ε : ℚ} {ε-pos : Positive ε} {x : Stream ℚ}
  → ε-Converge {ε} ε-pos x → ℕ
getN (ε-converge (fst , snd)) = fst

getProp : {ε : ℚ} {ε-pos : Positive ε} {x : Stream ℚ}
  → (conv : ε-Converge {ε} ε-pos x)
  ---------------------------------------------------
  → ∀ (n m : ℕ) → (getN conv) <ⁿ n → (getN conv) <ⁿ m
  → ∣ take m x - take n x ∣ < ε
getProp {ε} {ε-pos} {x} (ε-converge (fst , ε-n-converge p)) = p

sub-converge : {x : Stream ℚ} (picker : Picker)
               ----------------------------------
               → Cauthy x → Cauthy (sub picker x)
sub-converge {x} p (cauthy x-conv) = cauthy (λ {ε} → lemma {ε}) where
  lemma : {ε : ℚ} (ε-pos : Positive ε) →
    ε-Converge ε-pos (sub p x)
  lemma {ε} ε-pos = ε-converge (N , ε-n-converge lemma2) where
    N₁ = getN (x-conv {ε} ε-pos) 
    f = Picker.map p
    N = f N₁

    lemma2 : (n m : ℕ) → N <ⁿ n → N <ⁿ m
             → ∣ take m (sub p x) - take n (sub p x) ∣ < ε
    lemma2 n m N<n N<m =
      begin-strict
        ∣ yₘ - yₙ ∣
      ≡⟨ cong ∣_∣ (begin-equality
                     yₘ - yₙ
                   ≡⟨ cong (_- yₙ) (sub-take p x m) ⟩
                     xₚₘ - yₙ
                   ≡⟨ cong (xₚₘ -_) (sub-take p x n) ⟩
                     xₚₘ - xₚₙ
                   ∎
                   ) ⟩
        ∣ xₚₘ - xₚₙ ∣
      <⟨ getProp (x-conv {ε} ε-pos) (f n) (f m) N₁<pn N₁<pm ⟩
        ε ∎
      where
      yₘ = take m (sub p x)
      yₙ = take n (sub p x)
      xₚₘ = take (f m) x
      xₚₙ = take (f n) x
      N₁<pm : N₁ <ⁿ f m
      N₁<pm = begin-strict
              N₁   ≤⟨ n≤mono p N₁ ⟩
              N    ≤⟨ n≤mono p N ⟩
              f N  <⟨ aᵢ<aᵢ₊₁⇒mono< p N m N<m ⟩
              f m  ∎ where open ℕ.≤-Reasoning
      N₁<pn : N₁ <ⁿ f n
      N₁<pn = begin-strict
              N₁    ≤⟨ n≤mono p N₁ ⟩
              N    ≤⟨ n≤mono p N ⟩
              f N  <⟨ aᵢ<aᵢ₊₁⇒mono< p N n N<n ⟩
              f n  ∎ where open ℕ.≤-Reasoning
      open ℚ.≤-Reasoning
