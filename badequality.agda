module badequality where
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc; _<_; _≥_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties using (≤-reflexive; <⇒≱)

postulate
  f : ℕ → ℕ

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)

=≥ : {x y : ℕ} → x ≡ y → f x ≥ f y
=≥ x=y = ≤-reflexive (cong f (sym x=y))  

anti-cong : {x y : ℕ} → f x < f y → x ≢ y
anti-cong {x} {y} fx<fy = contraposition (=≥ {x} {y}) (<⇒≱ fx<fy)  