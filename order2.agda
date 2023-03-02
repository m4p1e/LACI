module order2 where
open import Data.Nat using (_≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂)

≤-antisym : ∀ m n → m ≤ n → n ≤ m → m ≡ m
-- ≤-antisym m n r₁ r₂ = refl
≤-antisym .zero n z≤n r₂ = refl
≤-antisym .(suc _) .(suc _) (s≤s r₁) (s≤s r₂) rewrite ≤-antisym _ _ r₁ r₂ = refl

-- a "trichotomy" theorem that says that for any two natural numbers m, n
-- exactly one of m < n, m = n , n < m holds. 
tri-the : ∀ m n → (m < n) ⊎ (m ≡ n) ⊎ (n < m)
tri-the zero zero = inj₂ (inj₁ refl)
tri-the zero (suc n) = inj₁ (s≤s z≤n)
tri-the (suc m) zero = inj₂ (inj₂ (s≤s z≤n))
tri-the (suc m) (suc n) with tri-the m n
... | inj₁ x = inj₁ (s≤s x)
... | inj₂ (inj₁ x) = inj₂ (inj₁ (cong suc x))
... | inj₂ (inj₂ y) = inj₂ (inj₂ (s≤s y))