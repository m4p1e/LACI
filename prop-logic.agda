module prop-logic where

{-
  C-c C-l          check file
  C-c C-SPC        check hole
  C-c C-,          display goal and context
  C-c C-c          split cases
  C-c C-r          fill in boilerplate from goal
  C-c C-d          display type of expression
  C-c C-v          evaluate expression (normally this is C-c C-n)
  C-c C-a          try to find proof automatically
  C-z              enable Vi keybindings
  C-x C-+          increase font size
  \bN \alpha \to   math symbols
-}

{-
test1 : ∀ {A B C : Set} → (A → B → C) → (A → B) → (A → C)
test1 = λ x x₁ x₂ → {!  !}
data Bool : Set where
    true : Bool
    false : Bool

data ℕ : Set where 
    Z : ℕ
    S : ℕ → ℕ
-}

-- introduction of ∧ 
data _∧_ (A B : Set) : Set where
    ∧-intro : A → B → A ∧ B

-- ∧ : precedence & right-associative 
infixr 2 _∧_

-- elimination1 of ∧ 
∧-elim₀ : ∀ {A B : Set} → A ∧ B → A
∧-elim₀ (∧-intro a b) = a

-- another form by pattern-matching lambda
∧-elim₀' : ∀ {A B : Set} → A ∧ B → A
∧-elim₀' = λ { (∧-intro a b) → a } 

-- elimination2 of ∧ 
∧-elim₁ : ∀ {A B : Set} → A ∧ B → B
∧-elim₁ (∧-intro a b) = b

-- proof of commutativity without elimination, function extensionality, η conversion.
∧-commut : ∀ {A B : Set} → A ∧ B → B ∧ A 
∧-commut (∧-intro a b) = ∧-intro b a

-- normal proof in natural deduction
∧-commut' : ∀ {A B : Set} → A ∧ B → B ∧ A 
∧-commut' = λ x → ∧-intro (∧-elim₁ x) (∧-elim₀ x)      

-- ex1: ((A ∧ B) → C) → (A → B → C)
formula₁ : ∀ {A B C : Set} → ((A ∧ B) → C) → (A → B → C) 
formula₁ c = λ a b → c (∧-intro a b)

-- ex2: (A → (B → C)) → ((A ∧ B) → C)
formula₂ : ∀ {A B C : Set} → (A → (B → C)) → ((A ∧ B) → C)
formula₂ c = λ x → c (∧-elim₀ x) (∧-elim₁ x)

-- ex3: (A → B) → ((A ∧ C) → (B ∧ C))
formula₃ : ∀ {A B C : Set} → (A → B) → ((A ∧ C) → (B ∧ C))
formula₃ c = λ x → ∧-intro (c (∧-elim₀ x)) (∧-elim₁ x)

-- ex4: ((A → B) ∧ (C → D)) → ((A ∧ C) → (B ∧ D))
formula₄ : ∀ {A B C D : Set} → ((A → B) ∧ (C → D)) → ((A ∧ C) → (B ∧ D))
formula₄ c = λ x → ∧-intro ((∧-elim₀ c) (∧-elim₀ x)) ((∧-elim₁ c) (∧-elim₁ x))

formula₄' : ∀ {A B C D : Set} → ((A → B) ∧ (C → D)) → ((A ∧ C) → (B ∧ D))
formula₄' x y = ∧-intro ((∧-elim₀ x) (∧-elim₀ y)) ((∧-elim₁ x) (∧-elim₁ y)) 

-- introduction of disconjunction
data _∨_ (A B : Set) : Set where
    ∨-introₒ : A → A ∨ B
    ∨-intro₁ : B → A ∨ B

-- ∨ : precedence & right-associative
infixr 1 _∨_

-- elimination ???? projection π₁/π₂
∨-elim : ∀ {A B C : Set} → (A ∨ A) → A
∨-elim (∨-introₒ x) = x
∨-elim (∨-intro₁ x) = x

-- proof of commutativity
∨-commut : ∀ {A B : Set} → (A ∨ B) → (B ∨ A)
∨-commut (∨-introₒ x) = ∨-intro₁ x
∨-commut (∨-intro₁ x) = ∨-introₒ x

-- ex5: (A → B ∨ C) → (B → D) → (C → D) → (A → D)
formula₅ : ∀ {A B C D : Set} → (A → B ∨ C) → (B → D) → (C → D) → (A → D)
formula₅ {A} {B} {C} {D} x y z w = helper (x w) 
    where 
        helper : B ∨ C → D
        helper (∨-introₒ x) = y x
        helper (∨-intro₁ x) = z x 

formula₅' : ∀ {A B C D : Set} → (A → B ∨ C) → (B → D) → (C → D) → (A → D)
formula₅' x y z w with x w
formula₅' x y z w | ∨-introₒ b = y b
formula₅' x y z w | ∨-intro₁ c = z c

-- ex6: (A → B) → ((A ∨ C) → (B ∨ C))
formula₆ : ∀ {A B C : Set} → (A → B) → ((A ∨ C) → (B ∨ C))
formula₆ x y with y
formula₆ x y | ∨-introₒ a = ∨-introₒ (x a)
formula₆ x y | ∨-intro₁ c = ∨-intro₁ c

-- ex7:  ((A ∨ B ) ∨ C) → (A ∨ (B ∨ C))
formula₇ : ∀ {A B C : Set} → ((A ∨ B ) ∨ C) → (A ∨ (B ∨ C))
formula₇ x with x 
formula₇ x | ∨-introₒ y with y
formula₇ x | ∨-introₒ y | ∨-introₒ a = ∨-introₒ a
formula₇ x | ∨-introₒ y | ∨-intro₁ b = ∨-intro₁ (∨-introₒ b)
formula₇ x | ∨-intro₁ c = ∨-intro₁ (∨-intro₁ c)

-- ex8: (A ∧ (B ∨ C)) → ((A ∨ C) ∧ (A ∨ B)) 
formula₈ : ∀ {A B C : Set} → (A ∧ (B ∨ C)) → ((A ∨ C) ∧ (A ∨ B))
formula₈ x = ∧-intro (∨-introₒ (∧-elim₀ x)) (∨-introₒ (∧-elim₀ x))