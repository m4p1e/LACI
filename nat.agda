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