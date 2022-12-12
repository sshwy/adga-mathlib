{-# OPTIONS --guardedness #-}

module Experimental.Sshwy.RationalCauthy where

open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ⁿ_)
import Data.Nat.Properties as ℕ
open import Data.Rational using (ℚ; 0ℚ; _<_; _-_; ∣_∣; Positive)
import Data.Rational.Properties as ℚ
open import Data.Product using (∃; Σ; Σ-syntax; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)

-- import Data.Integer.Base as ℤ -- for better agda-mode output
-- open ℚ renaming (numerator to ↥_; denominator to ↧_)

open import Stream using (Stream; Picker; sub; take; repeat; const; _,_; _∷_)


Conv : Stream ℚ → Set
Conv x = ∀ (e : ℚ) (e-pos : Positive e) → Σ[ N ∈ ℕ ] (∀ (n m : ℕ) → N <ⁿ n → N <ⁿ m → ∣ take m x - take n x ∣ < e)

≡⇒0 : {x y : ℚ} → x ≡ y → x - y ≡ 0ℚ
≡⇒0 {x} {y} x=y = trans (cong (_- y) x=y) (ℚ.+-inverseʳ y)

-- cauthy sequence of rational numbers
record Cauthy : Set where
  constructor _,_
  field
    seq : Stream ℚ
    isConv : Conv seq

module _ where
  open Cauthy
  open import Stream.Properties using (f=S; sub-take; n≤mono; aᵢ<aᵢ₊₁⇒mono<)
  
  private
    lemma : (ε : ℚ) (ε-pos : Positive ε) (x : ℚ)
      → (n m : ℕ)
      → zero <ⁿ n
      → zero <ⁿ m
      ---------------
      → ∣ take m (repeat x) - take n (repeat x) ∣ < ε
    lemma ε ε-pos x n m N<n N<m =
      begin-strict
        ∣ xₘ - xₙ ∣ ≡⟨ cong ∣_∣ (≡⇒0 (begin-equality
             xₘ ≡⟨ f=S (const x) m ⟩
             x  ≡˘⟨ f=S (const x) n ⟩
             xₙ ∎))⟩
        0ℚ <⟨ ℚ.positive⁻¹ ε-pos ⟩
      ε ∎
      where
      open ℚ.≤-Reasoning
      xₘ = take m (repeat x)
      xₙ = take n (repeat x)

  -- construct a cauthy sequence from ℚ
  ℚ-Cauthy : ℚ → Cauthy
  seq (ℚ-Cauthy x) = repeat x
  isConv (ℚ-Cauthy x) e e-pos = zero , lemma e e-pos x

  subseq : Picker → Cauthy → Cauthy
  subseq p@(f , isMono) (xs , xs-conv) = sub p xs , isconv where
    isconv : Conv (sub p xs)
    isconv e e-pos = N , proof where
      N₁ = proj₁ (xs-conv e e-pos)
      N = f N₁

      proof :  (n m : ℕ) → N <ⁿ n → N <ⁿ m → ∣ take m (sub p xs) - take n (sub p xs) ∣ < e
      proof n m N<n N<m = begin-strict
          ∣ yₘ - yₙ ∣
        ≡⟨ cong ∣_∣ (begin-equality
                       yₘ - yₙ
                     ≡⟨ cong (_- yₙ) (sub-take p xs m) ⟩
                       xₚₘ - yₙ
                     ≡⟨ cong (xₚₘ -_) (sub-take p xs n) ⟩
                       xₚₘ - xₚₙ
                     ∎
                     ) ⟩
          ∣ xₚₘ - xₚₙ ∣
        <⟨ proj₂ (xs-conv e e-pos) (f n) (f m) N₁<pn N₁<pm ⟩
          e
        ∎ where
        yₘ = take m (sub p xs)
        yₙ = take n (sub p xs)
        xₚₘ = take (f m) xs
        xₚₙ = take (f n) xs
        N₁<pm : N₁ <ⁿ f m
        N₁<pm = begin-strict
                N₁   ≤⟨ n≤mono p N₁ ⟩
                N    ≤⟨ n≤mono p N ⟩
                f N  <⟨ aᵢ<aᵢ₊₁⇒mono< p N m N<m ⟩
                f m  ∎ where open ℕ.≤-Reasoning
        N₁<pn : N₁ <ⁿ f n
        N₁<pn = begin-strict
                N₁   ≤⟨ n≤mono p N₁ ⟩
                N    ≤⟨ n≤mono p N ⟩
                f N  <⟨ aᵢ<aᵢ₊₁⇒mono< p N n N<n ⟩
                f n  ∎ where open ℕ.≤-Reasoning
        open ℚ.≤-Reasoning
