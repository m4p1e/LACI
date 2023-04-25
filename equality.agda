module equality where
open import Data.Bool

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

a : Bool
a = false
b = a

-- definitional equality => propositions equality
defeq : a ≡ b
defeq = refl

≡-sym : ∀ {A : Set} {x y : A } → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

cong : ∀ {A B : Set} {f : A → B} {x y : A} → x ≡ y → f x ≡ f y
cong {A} {B} {f} {x} {.x} refl = refl

subst : ∀ {A : Set} {P : A → Set} {x y : A} → x ≡ y → P x → P y
subst {A} {p} {x} {.x} refl px = px


-- ???
-- ?funext : ∀ {A B : Set} {f g : A → B} (a : A) → f a ≡ g a → f ≡ g
-- ?funext {A} {B} {f} {g} a r = ?

