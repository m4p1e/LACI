module nat where
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; suc; zero)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 6 _+_

-- left identity is directly from definitional equality
rid : ∀ (n : ℕ) → (n + zero) ≡ n
rid zero = refl
rid (suc n) = cong suc (rid n)

rid₁ : ∀ (n : ℕ) → (n + zero) ≡ n
rid₁ zero = refl
rid₁ (suc n) with n + zero | rid₁ n
... | .n | refl = refl

-- rewrite keyword is syntactic sugar of with
-- here apply a propositional equality by rewrite
rid₂ : ∀ (n : ℕ) → (n + zero) ≡ n
rid₂ zero = refl
rid₂ (suc n) rewrite rid₂ n = refl

-- 0 + m ≡ m and n + suc m ≡ suc (n + m) 
+suc : ∀ n m → (n + suc m) ≡ suc (n + m)
+suc zero m = refl
+suc (suc n) m rewrite +suc n m = refl

-- (n + m) ≡ (m + n)
+comm : ∀ n m → (n + m) ≡ (m + n)
+comm zero m rewrite rid m = refl 
+comm (suc n) m rewrite +suc m n = cong suc (+comm n m)

-- a + (b + c) ≡ (a + b) + c
+assoc : ∀ a b c → (a + (b + c)) ≡ ((a + b) + c)
+assoc zero b c = refl
+assoc (suc a) b c rewrite +assoc a b c = refl




