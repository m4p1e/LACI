module identity where
open import Relation.Binary.PropositionalEquality

Indiscernibility : (A : Set) →  (C : A → Set) → (x y : A) → x ≡ y → (C x → C y)

Indiscernibility A C x y x=y rewrite x=y = λ cx → cx

PathInduction : {A : Set} 
              → (C : (x : A) → (y : A) → x ≡ y → Set)
              → (c : (x : A) → (x=x : x ≡ x) → C x x x=x)
              → (x : A) → (y : A) → (p : x ≡ y) → C x y p 

PathInduction C c x x refl = c x refl