{-# OPTIONS --guardedness #-}

module Experimental.Sshwy.Nats where

open import Ext.Stream
open import Ext.Stream.Properties using (f=S; _≡S_)
open Ext.Stream.Stream

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Nat.Properties using (+-identityʳ; +-suc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)

-- start from k
k-seqℕ : (k : ℕ) → Stream ℕ
hd (k-seqℕ k) = k
tl (k-seqℕ k) = k-seqℕ (k + 1)

k-seqℕ[n]=n+k : ∀ (k n : ℕ) → take n (k-seqℕ k) ≡ k + n
k-seqℕ[n]=n+k k zero rewrite +-identityʳ k = refl
k-seqℕ[n]=n+k k (suc n) rewrite +-suc k n | +-suc k zero | +-identityʳ k 
  = k-seqℕ[n]=n+k (suc k) n

-- natural numbers
seqℕ : Stream ℕ
seqℕ = k-seqℕ 0

seqℕₙ=n : ∀ (n : ℕ) → take n seqℕ ≡ n
seqℕₙ=n = k-seqℕ[n]=n+k 0

fib : ℕ → ℕ
fib zero = 0
fib (suc zero) = 1
fib (suc (suc n)) = fib n + fib (suc n)

fibs : Stream ℕ
fibs = f→S fib

seqℕ-f : Stream ℕ
seqℕ-f = f→S λ n → n

seqℕ-f=seqℕ[n] : (n : ℕ) → take n seqℕ-f ≡ take n seqℕ
seqℕ-f=seqℕ[n] n rewrite seqℕₙ=n n | f=S (λ x → x) n = refl

seqℕ-f=seqℕ : seqℕ-f ≡S seqℕ
seqℕ-f=seqℕ = _≡S_.eqS seqℕ-f=seqℕ[n]
