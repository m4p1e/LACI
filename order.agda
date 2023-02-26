module order where

{-
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl