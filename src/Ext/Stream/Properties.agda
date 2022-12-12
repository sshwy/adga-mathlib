{-# OPTIONS --guardedness #-}

module Ext.Stream.Properties where

open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _≤_)
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open import Ext.Stream.Base public
open Ext.Stream.Base.Stream

-- equality on stream
data _≡S_ {A : Set} : Rel (Stream A) 0ℓ where
  eqS : {as bs : Stream A} (f : ∀ (n : ℕ) → take n as ≡ take n bs) 
    -------------------------------------------
    → as ≡S bs

≡S-refl : {A : Set} → Reflexive (_≡S_ {A})
≡S-refl = eqS (λ n → refl)

≡S-sym : {A : Set} → Symmetric (_≡S_ {A})
≡S-sym (eqS f) = eqS (λ n → sym (f n))

≡S-trans : {A : Set} → Transitive (_≡S_ {A})
≡S-trans (eqS f) (eqS g) = eqS (λ n → trans (f n) (g n))

-- ≡S is a setoid
≡S-setoid : (A : Set) → Setoid 0ℓ 0ℓ
Setoid.Carrier (≡S-setoid A) = Stream A
Setoid._≈_ (≡S-setoid A) = _≡S_
Setoid.isEquivalence (≡S-setoid A) = record {
  refl = ≡S-refl ;
  sym = ≡S-sym ;
  trans = ≡S-trans
  }

≡S-cong-map : {A B : Set} (f : ℕ → A → B) {as bs : Stream A}
  → as ≡S bs
  ---------------
  → ∀ (n : ℕ) → f n (take n as) ≡ f n (take n bs)
≡S-cong-map f (eqS aₙ=bₙ) n = cong (f n) (aₙ=bₙ n)

f=S : {A : Set} (f : (n : ℕ) → A)
      → ∀ (n : ℕ) → take n (f→S f) ≡ f n
f=S f zero = refl
f=S f (suc n) = f=S (λ n₁ → f(suc n₁)) n

take-tl : {A : Set} (n : ℕ) (as : Stream A)
  -----------------------------------------
  → take (suc n) as ≡ take n (tl as)
take-tl = λ n as → refl

≡S-tl : {A : Set} {as bs : Stream A}
  → as ≡S bs
  ----------------
  → tl as ≡S tl bs
≡S-tl {A} {as} {bs} (eqS g) = eqS λ n →
  begin
    take n (tl as)
  ≡⟨ take-tl n as ⟩
    take (suc n) as
  ≡⟨ g (suc n) ⟩
    take (suc n) bs
  ≡˘⟨ take-tl n bs ⟩
    take n (tl bs)
  ∎  where open Eq.≡-Reasoning

zipWith-tl : {A B C : Set} (f : A → B → C)
  (as : Stream A) (bs : Stream B) (cs : Stream C)
  ---------------------------------------------------
  → tl (zipWith f as bs) ≡S zipWith f (tl as) (tl bs)
zipWith-tl _ _ _ _ = eqS (λ _ → refl)

zipWith-take : {A B C : Set} (f : A → B → C)
  (as : Stream A) (bs : Stream B) (cs : Stream C)
  → cs ≡S zipWith f as bs
  ---------------------------------------------------
  → ∀ (n : ℕ) → take n cs ≡ f (take n as) (take n bs)
zipWith-take f as bs cs (eqS g) zero = g zero
zipWith-take f as bs cs p (suc n) =
  zipWith-take f (tl as) (tl bs) (tl cs)
    (≡S-trans (≡S-tl p) (zipWith-tl f as bs cs)) n
 
sub-take : {A : Set} (p@(f , _) : Picker) (x : Stream A)
           -------------------------------------------
           → ∀ (n : ℕ) → take n (sub p x) ≡ take (f n) x
sub-take p@(f , _) x = f=S (λ n → take (f n) x)

suc=tl : {A : Set} (as : Stream A) → sub picker-tl as ≡S tl as
suc=tl {A} as = eqS (λ n → begin
                             take n (sub picker-tl as)
                           ≡⟨ sub-take picker-tl as n ⟩
                             take (suc n) as
                           ≡⟨ take-tl n as ⟩
                             take n (tl as)
                           ∎) where open Eq.≡-Reasoning

aᵢ<aᵢ₊₁⇒mono≤ : (pi@(f , f-suc) : Picker)
               -------------------------------------------
               → ∀ (p q : ℕ) → p ≤ q → f p ≤ f q
aᵢ<aᵢ₊₁⇒mono≤ pi@(f , f-suc)  p q x with q | ℕ.≤⇒≤′ x
... | .p | Data.Nat.≤′-refl = ℕ.≤-refl
... | (suc n) | Data.Nat.≤′-step r =
  begin
    f p
  ≤⟨ aᵢ<aᵢ₊₁⇒mono≤ pi p n (ℕ.≤′⇒≤ r) ⟩
    f n
  <⟨ f-suc n ⟩
    f (suc n)
  ∎ where open ℕ.≤-Reasoning

aᵢ<aᵢ₊₁⇒mono< : (pi@(f , f-suc) : Picker)
               -------------------------------------------
               → ∀ (p q : ℕ) → p < q → f p < f q
aᵢ<aᵢ₊₁⇒mono< pi@(f , f-suc) p (suc q) (s≤s x) =
  begin-strict
    f p
  ≤⟨ aᵢ<aᵢ₊₁⇒mono≤ pi p q x ⟩
    f q
  <⟨ f-suc q ⟩
    f (suc q)
  ∎ where open ℕ.≤-Reasoning

n≤mono : (pi@(f , f-suc) : Picker)
         → ∀ (n : ℕ) → n ≤ f n
n≤mono _ zero = z≤n
n≤mono p@(_ , f-suc) (suc n) = ℕ.≤-trans (s≤s (n≤mono p n)) (f-suc n)
