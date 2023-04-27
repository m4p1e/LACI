module identity where
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (Bool; true; false)

Indiscernibility : {A : Set} →  {C : A → Set} → {x y : A} → x ≡ y → (C x → C y)
-- Indiscernibility x=y rewrite x=y = λ cx → cx
Indiscernibility refl = λ cx → cx 

PathInduction :{A : Set} 
              → (C : (x : A) → (y : A) → x ≡ y → Set₁)
              → (c : (x : A) → C x x refl)
              → (x : A) → (y : A) → (p : x ≡ y) → C x y p 

PathInduction C c x x refl = c x


PathInduction₁ : {A : Set} {a : A} 
              → (C : a ≡ a → Set)
              → (c : C refl)
              →  C refl  

PathInduction₁ C c = c 

BasePathInduction : {A : Set} 
                → (a : A) 
                → (C : (x : A) → a ≡ x → Set)
                → (c : C a refl)
                → (x : A) → (p : a ≡ x) → C x p

BasePathInduction a C c x refl = c

BasePathInduction⇒PathInduction : {A : Set}

                                → ((a : A) 
                                    → (C : (x : A) → a ≡ x → Set)
                                    → (c : C a refl)
                                    → (x : A) → (p : a ≡ x) → C x p)

                                → ((C : (x : A) → (y : A) → x ≡ y → Set)
                                    → (c : (x : A) → C x x refl)
                                    → (x : A) → (y : A) → (p : x ≡ y) → C x y p) 

BasePathInduction⇒PathInduction bpi C c x y p with C x | c x 
... | C₁ | c₁ = bpi x C₁ c₁ y p

PathInduction⇒BasePathInduction :{A : Set}

                                → ((C : (x : A) → (y : A) → x ≡ y → Set)
                                    → (c : (x : A) → C x x refl)
                                    → (x : A) → (y : A) → (p : x ≡ y) → C x y p)
                                
                                → ((a : A) 
                                    → (C : (x : A) → a ≡ x → Set)
                                    → (c : C a refl)
                                    → (x : A) → (p : a ≡ x) → C x p)

PathInduction⇒BasePathInduction pi a C c x p = f a x p C c where
-- construct a family of x y p
    D : {A : Set} → (x y : A) → x ≡ y → Set₁
    D {A} x y p = (C : (z : A) → x ≡ z → Set) → (C x refl → C y p)
-- By use path induction to construct f, we need d 
    d : {A : Set} → ((x : A) → D x x refl)
    d x C c = c

    f : {A : Set} → (x y : A) → (p : x ≡ y) → D x y p
    f = PathInduction D d

postulate
    x : Set
    y : Set

eq₁ : x ≡ x → Set
eq₁ refl = x

eq₂ : {z : Set} → x ≡ z → Set
eq₂ refl = x

eq₃ : x ≡ y → Set
eq₃ x=y = {!  !}


K : {a : Set} → (P : a ≡ a →  Set) → (p : P refl) → (e : a ≡ a) → P e
K P p refl = p

coerce : Bool ≡ Bool → Bool → Bool
coerce refl a = a 

coerce-id : (e : Bool ≡ Bool) → coerce e true ≡ true
coerce-id refl = refl

f : Bool → Bool
f true = true
f false = false

g : Bool → Bool
g true = true
g false = false

_ : f ≡ g
_ = {!   !}   