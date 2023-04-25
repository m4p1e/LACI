module fin where

open import Data.Nat using (ℕ; zero; suc)

-- There are excactly n elements belong to Fin(n), how to define ? amazing
Fin : ℕ → Set 
Fin zero = {!   !}
Fin (suc n) = {!   !}