{-# OPTIONS --guardedness #-}

module Reals where

open import Data.Bool using (Bool; true; false)

open import Real

data ℝ-set : Set where
  predictor : (p : (x : ℝ) → Bool) → ℝ-set

