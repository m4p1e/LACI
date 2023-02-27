module order where

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

-- first case for recurison
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n r2 = z≤n
≤-trans (s≤s r1) (s≤s r2) = s≤s (≤-trans r1 r2)

≤-total : ∀ (m n : ℕ) → (m ≤ n) ⊎ (n ≤ m)
≤-total zero n = inj₁ z≤n
≤-total (suc m) zero = inj₂ z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | inj₁ x = inj₁ (s≤s x)
... | inj₂ y = inj₂ (s≤s y)

-- strict inequality
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : ¬ P → Dec P


-- counterexample is also available
¬∀m≤n : ¬ ∀ (m n : ℕ) → m ≤ n
¬∀m≤n x with x 1 zero
... | ()

?∀m≤n : ∀ (m n : ℕ) → Dec (m ≤ n)
?∀m≤n zero zero = yes z≤n
?∀m≤n (suc m) zero = no λ x → {!   !}
?∀m≤n zero (suc n) = yes z≤n
?∀m≤n (suc m) (suc n) = {!   !} 
