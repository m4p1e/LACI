module div where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)

data _∣_ : ℕ → ℕ → Set where
    0∣0 : zero ∣ zero
    m∣0 : ∀ {d} → suc d ∣ zero
    m∣n : ∀ {d m} → suc d ∣ m → suc d ∣ suc (m + d)

infix 4 _∣_

∣-refl : ∀ a → a ∣ a
∣-refl zero = 0∣0
∣-refl (suc a) = m∣n m∣0

+zero : ∀ m → m + zero ≡ m
+zero zero = refl
+zero (suc m) rewrite +zero m = refl

+n : ∀ {m n : ℕ} → m + suc n ≡ suc (m + n)
+n {zero} {n} = refl
+n {suc m} {n} = cong suc (+n)

d-suc : ∀ {m n : ℕ} → suc (m + suc n) ≡ suc (suc (m + n))
d-suc = cong suc (+n)

++ex : ∀ {a b c : ℕ} → a + b + c ≡ a + c + b
++ex {zero} {b} {c} rewrite +-comm b c = refl
++ex {suc a} {b} {c} = cong suc (++ex {a} {b} {c})

div1 : ∀ {m : ℕ} → 1 ∣ m
div1 {zero} = m∣0
div1 {suc m} with m∣n (div1 {m})
... | s rewrite +-identityʳ m = s
 
test : ∀ a b → a ∣ b → a ∣ (b + a)
test zero zero r₁ = 0∣0
test (suc a) zero r₁ = m∣n r₁
test (suc a) (suc b) r₁ with m∣n r₁
... | s rewrite d-suc {b} {a} = s

++ex1 : ∀ {d m c w} → w ≡ m + d → w + c ≡ m + c + d
++ex1 {d} {m} {c} {.(m + d)} refl = ++ex {m} {d} {c}  

∣-plus : ∀ a b c → a ∣ b → a ∣ c → a ∣ b + c
∣-plus .zero .zero c 0∣0 r₂ = r₂
∣-plus .(suc _) .zero c m∣0 r₂ = r₂
∣-plus (suc d) (suc w) c (m∣n r₁) r₂ with m∣n (∣-plus _ _ _ r₁ r₂)
... | s rewrite ++ex1 {d} {_} {c} {w} refl = s

+ex1 : ∀ {b m w} → w ≡ m + b → w ≡ b + m
+ex1 {b} {m} {w} refl rewrite +-comm m b = refl

∣-trans : ∀ a b c → a ∣ b → b ∣ c → a ∣ c
∣-trans a zero zero r₁ 0∣0 = r₁
∣-trans (suc a) (suc b) zero r₁ m∣0 = m∣0
∣-trans _ (suc b) (suc w) r₁ (m∣n r₂) with ∣-plus _ _ _ r₁ (∣-trans _ _ _ r₁ r₂)
... | s rewrite +ex1 {b} {_} {w} refl = s
