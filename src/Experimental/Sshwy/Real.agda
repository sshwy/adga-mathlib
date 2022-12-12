{-# OPTIONS --guardedness #-}

module Experimental.Sshwy.Real where

open import Agda.Builtin.Unit using (tt)

open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_<_ to _<ⁿ_)
import Data.Nat.Properties as ℕ-prop
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
import Data.Rational.Properties as ℚ-prop
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open import Data.Product using (∃; Σ; Σ-syntax; _,_; proj₁; proj₂)

-- for better agda-mode output
import Data.Integer.Base as ℤ 
open ℚ.ℚ renaming (numerator to ↥_; denominator to ↧_)

open import Stream using (Stream; take; repeat; zipWith)
open import Stream.Properties using (zipWith-take; _≡S_)
open import Experimental.Sshwy.RationalCauthy as RC using (Cauthy; _,_)

ℝ : Set
ℝ = Cauthy

-- take the n-th element of r's sequence
takeℝ : ℕ → ℝ → ℚ
takeℝ n (seq , isConv) = take n seq

ℚ→ℝ : ℚ → ℝ
ℚ→ℝ x = RC.ℚ-Cauthy x

0ℝ : ℝ
0ℝ = ℚ→ℝ 0ℚ

module ℚ-lem where
  open import Data.Rational using (_+_; _-_; -_)
  open ℚ-prop
  open ℚ-prop.≤-Reasoning
    
  lemma-abcd : (a b c d : ℚ) → (a + b) - (c + d) ≡ (a - c) + (b - d)
  lemma-abcd a b c d =
    begin-equality
      (a + b) - (c + d)
    ≡⟨ cong (a + b +_) (neg-distrib-+ c d) ⟩
      (a + b) + (- c - d)
    ≡˘⟨ +-assoc (a + b) (- c) (- d) ⟩
      a + b - c - d
    ≡⟨ cong (_+ (- d)) (+-assoc a b (- c)) ⟩
      a + (b - c) - d
    ≡⟨ cong (λ x → a + x - d) (+-comm b (- c)) ⟩
      a + (- c + b) - d
    ≡˘⟨ cong (_- d) (+-assoc a (- c) b) ⟩
      a - c + b - d
    ≡⟨ +-assoc (a - c) b (- d) ⟩
      (a - c) + (b - d)
    ∎

_+_ : ℝ → ℝ → ℝ
(as , a-conv) + (bs , b-conv) = cs , c-conv where
  cs : Stream ℚ
  cs = zipWith ℚ._+_ as bs

  cₙ=aₙ+bₙ : (n : ℕ) → take n cs ≡ take n as ℚ.+ take n bs
  cₙ=aₙ+bₙ = zipWith-take ℚ._+_ as bs cs (_≡S_.eqS (λ n → refl))
  
  c-conv : RC.Conv cs
  c-conv ε ε-pos = N , proof where
    open import Data.Rational using (_<_; ∣_∣; _-_; -_; ½; _*_; Positive; positive)
    ε>0 : 0ℚ < ε
    ε>0 = ℚ-prop.positive⁻¹ ε-pos

    ½ε : ℚ
    ½ε = ε * ½

    ½ε-pos : Positive ½ε
    ½ε-pos = positive (ℚ-prop.*-monoˡ-<-pos ½ tt ε>0)

    Nᵃ = proj₁ (a-conv ½ε ½ε-pos)
    Nᵇ = proj₁ (b-conv ½ε ½ε-pos)
    N = Nᵃ ⊔ Nᵇ

    proof : (n m : ℕ) → N <ⁿ n → N <ⁿ m
      ---------------------------------
      → ∣ take m cs - take n cs ∣ < ε
    proof n m N<n N<m =
      begin-strict
        ∣ cₘ - cₙ ∣
      ≡⟨ cong ∣_∣ (begin-equality
                     cₘ - cₙ
                   ≡⟨ cong (_- cₙ) (cₙ=aₙ+bₙ m) ⟩
                     aₘ ℚ.+ bₘ - cₙ
                   ≡⟨ cong (λ x → aₘ ℚ.+ bₘ - x) (cₙ=aₙ+bₙ n) ⟩
                     aₘ ℚ.+ bₘ - (aₙ ℚ.+ bₙ)
                   ≡⟨ ℚ-lem.lemma-abcd aₘ bₘ aₙ bₙ ⟩
                     (aₘ - aₙ) ℚ.+ (bₘ - bₙ)
                   ∎) ⟩
        ∣ (aₘ - aₙ) ℚ.+ (bₘ - bₙ) ∣
      ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (aₘ - aₙ) (bₘ - bₙ)  ⟩
        ∣ aₘ - aₙ ∣ ℚ.+ ∣ bₘ - bₙ ∣
      <⟨ +-mono-< |aₘ-aₙ|<½ε |bₘ-bₙ|<½ε ⟩
        ½ε ℚ.+ ½ε
      ≡˘⟨ *-distribˡ-+ ε ½ ½ ⟩
        ε * 1ℚ
      ≡⟨ *-identityʳ ε ⟩
        ε
      ∎

      where
        open ℚ-prop
        aₙ = take n as
        aₘ = take m as
        bₙ = take n bs
        bₘ = take m bs
        cₙ = take n cs
        cₘ = take m cs
        
        Nᵃ<n = ℕ-prop.m⊔n<o⇒m<o Nᵃ Nᵇ N<n
        Nᵃ<m = ℕ-prop.m⊔n<o⇒m<o Nᵃ Nᵇ N<m
      
        |aₘ-aₙ|<½ε : ∣ aₘ - aₙ ∣ < ½ε
        |aₘ-aₙ|<½ε = proj₂ (a-conv ½ε ½ε-pos) n m Nᵃ<n Nᵃ<m

        Nᵇ<n = ℕ-prop.m⊔n<o⇒n<o Nᵃ Nᵇ N<n
        Nᵇ<m = ℕ-prop.m⊔n<o⇒n<o Nᵃ Nᵇ N<m

        |bₘ-bₙ|<½ε : ∣ bₘ - bₙ ∣ < ½ε
        |bₘ-bₙ|<½ε = proj₂ (b-conv ½ε ½ε-pos) n m Nᵇ<n Nᵇ<m
        
        open ℚ-prop.≤-Reasoning
