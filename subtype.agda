module subtype where
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_)
open import Relation.Nullary using (Dec; yes; no; _because_)
open import Data.Product using (Σ; Σ-syntax)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)


data sec_ (a : ℕ) : Set where

_<:₂?_ : {a b : ℕ} → sec a → sec b → Bool  
_<:₂?_ {a} {b} _ _ with a ≤? b 
... | false because proof = false
... | true because proof = true 



P : (ℕ × ℕ) → Set
P p = Bool
-- P p with (proj₁ p) ≤? (proj₂ p) 
-- ... | false because proof = Bool
-- ... | true because proof = Bool

cert : (p : (ℕ × ℕ)) → (P p) ≡ Bool
cert p = refl

_<:_ : (a : ℕ) → (b : ℕ) → Σ (ℕ × ℕ) P
a <: b rewrite cert (a , b) = (a , b) , true 