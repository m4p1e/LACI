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

-- proof of commutativity 
∧-commut : ∀ {A B : Set} → A ∧ B → B ∧ A 
∧-commut (∧-intro a b) = ∧-intro b a 

