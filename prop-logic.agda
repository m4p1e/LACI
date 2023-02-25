module prop-logic where

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
∧-formula₁ : ∀ {A B C : Set} → ((A ∧ B) → C) → (A → B → C) 
∧-formula₁ c = λ a b → c (∧-intro a b)

-- ex2: (A → (B → C)) → ((A ∧ B) → C)
∧-formula₂ : ∀ {A B C : Set} → (A → (B → C)) → ((A ∧ B) → C)
∧-formula₂ c = λ x → c (∧-elim₀ x) (∧-elim₁ x)

-- ex3: (A → B) → ((A ∧ C) → (B ∧ C))
∧-formula₃ : ∀ {A B C : Set} → (A → B) → ((A ∧ C) → (B ∧ C))
∧-formula₃ c = λ x → ∧-intro (c (∧-elim₀ x)) (∧-elim₁ x)

-- ex4: ((A → B) ∧ (C → D)) → ((A ∧ C) → (B ∧ D))
∧-formula₄ : ∀ {A B C D : Set} → ((A → B) ∧ (C → D)) → ((A ∧ C) → (B ∧ D))
∧-formula₄ c = λ x → ∧-intro ((∧-elim₀ c) (∧-elim₀ x)) ((∧-elim₁ c) (∧-elim₁ x))

∧-formula₄' : ∀ {A B C D : Set} → ((A → B) ∧ (C → D)) → ((A ∧ C) → (B ∧ D))
∧-formula₄' x y = ∧-intro ((∧-elim₀ x) (∧-elim₀ y)) ((∧-elim₁ x) (∧-elim₁ y)) 

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
∨-formula₁ : ∀ {A B C D : Set} → (A → B ∨ C) → (B → D) → (C → D) → (A → D)
∨-formula₁ {A} {B} {C} {D} x y z w = helper (x w) 
    where 
        helper : B ∨ C → D
        helper (∨-introₒ x) = y x
        helper (∨-intro₁ x) = z x 

∨-formula₂' : ∀ {A B C D : Set} → (A → B ∨ C) → (B → D) → (C → D) → (A → D)
∨-formula₂' x y z w with x w
∨-formula₂' x y z w | ∨-introₒ b = y b
∨-formula₂' x y z w | ∨-intro₁ c = z c

-- ex6: (A → B) → ((A ∨ C) → (B ∨ C))
∨-formula₃ : ∀ {A B C : Set} → (A → B) → ((A ∨ C) → (B ∨ C))
∨-formula₃ x y with y
∨-formula₃ x y | ∨-introₒ a = ∨-introₒ (x a)
∨-formula₃ x y | ∨-intro₁ c = ∨-intro₁ c

-- ex7:  ((A ∨ B ) ∨ C) → (A ∨ (B ∨ C))
∨-formula₄ : ∀ {A B C : Set} → ((A ∨ B ) ∨ C) → (A ∨ (B ∨ C))
∨-formula₄ x with x 
∨-formula₄ x | ∨-introₒ y with y
∨-formula₄ x | ∨-introₒ y | ∨-introₒ a = ∨-introₒ a
∨-formula₄ x | ∨-introₒ y | ∨-intro₁ b = ∨-intro₁ (∨-introₒ b)
∨-formula₄ x | ∨-intro₁ c = ∨-intro₁ (∨-intro₁ c)

-- ex8: (A ∧ (B ∨ C)) → ((A ∨ C) ∧ (A ∨ B)) 
∨-formula₅ : ∀ {A B C : Set} → (A ∧ (B ∨ C)) → ((A ∨ C) ∧ (A ∨ B))
∨-formula₅ x = ∧-intro (∨-introₒ (∧-elim₀ x)) (∨-introₒ (∧-elim₀ x))


-- top/true
data ⊤ : Set where
    tt : ⊤ 

-- bot/false
data ⊥ : Set where

-- elimination of ⊥
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- negation is function, but why? it is actually a notational definition, 
-- but not new definition
¬ : Set → Set
¬ A = A → ⊥ 

-- ex9: ⊥ ∨ A → A
⊥-formula₁ : ∀ {A : Set} → ⊥ ∨ A → A
-- case: ∨-introₒ ⊥ is impossible 
⊥-formula₁ (∨-intro₁ x) = x

-- ex10: A ∧ ¬ A → B
¬-formula₁ : ∀ {A B : Set} → A ∧ ¬ A → B
¬-formula₁ (∧-intro x x₁) = ⊥-elim (x₁ x)

-- ex11: (A → B) → ((¬ B) → (¬ A))
prop-fol₁ : ∀ {A B : Set} → (A → B) → ((¬ B) → (¬ A))
prop-fol₁ x y = λ a → y (x a)

-- ex12: (¬ (A ∨ B)) → (A → B)
prop-fol₂ : ∀ {A B : Set} → (¬ (A ∨ B)) → (A → B)
prop-fol₂ x = λ a → ⊥-elim(x (∨-introₒ a))

-- ex13: (A → (B ∨ C))→ ((¬ B) → ((¬ C) → (¬ A)))
prop-fol₃ : ∀ {A B C : Set} → (A → (B ∨ C))→ ((¬ B) → ((¬ C) → (¬ A)))
prop-fol₃ x y z a with x a
prop-fol₃ x y z a | ∨-introₒ b = y b
prop-fol₃ x y z a | ∨-intro₁ c = z c

-- ex14: (¬ (A ∨ B)) → ((¬ A) ∨ (¬ B))
-- better case for understanding interactive proof assistant
prop-fol₄ : ∀ {A B : Set} → (¬ (A ∨ B)) → ((¬ A) ∨ (¬ B))
prop-fol₄ x = ∨-introₒ (λ a → x (∨-introₒ a))


-- ∀ distributes over conjunction
∀-dist-∧ : ∀ (A : Set) (B C : A → Set) 
            → (∀ (a : A) → B a ∧ C a) 
            → (∀ (a : A) → B a) ∧ (∀ (a : A) → C a)

∀-dist-∧ A B C x = ∧-intro (λ a → ∧-elim₀ (x a)) (λ a → ∧-elim₁ (x a))


data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (x : A) → B x → Σ A B

Σ-syntax = Σ 
infix 2 Σ-syntax 
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- 1st projection of Σ  
fst : ∀ {A : Set} {B : A → Set} → Σ A B → A 
fst (a , ba) = a

-- 2st projection of Σ
snd : ∀ {A : Set} {B : A → Set} → ∀ (p : Σ A B) → B (fst p)    
snd (a , ba) = ba

-- ex15 : ∃x B x → ¬ ∀x ¬ B x 
∃e¬∀¬ : ∀ {A : Set} {B : A → Set} → ∃[ x ] B x → (¬ ∀ x → ¬ (B x))
∃e¬∀¬ = λ f g → g (fst f) (snd f)

-- ex16 : ¬ ∃x B x → ∀x ¬ B x 
¬∃e∀¬ : ∀ {A : Set} {B : A → Set} → ¬ (∃[ x ] B x) → (∀ x → ¬ (B x))
¬∃e∀¬ = λ f a ba → f (a , ba)

-- ex17 : ∃x ¬ (B x) → ¬ ∀x B x
∃¬e¬∀ : ∀ {A : Set} {B : A → Set} → ∃[ x ] ¬ (B x) → ¬ ∀ x → B x
∃¬e¬∀ = λ f g → snd f (g (fst f))

∃-distr-∨ : ∀ {A : Set} {B C : A → Set}
             → ∃[ x ] (B x ∨ C x) → (∃[ x ] B x) ∨ (∃[ x ] C x)
∃-distr-∨ x with snd x
∃-distr-∨ x | ∨-introₒ f = ∨-introₒ (fst x , f)
∃-distr-∨ x | ∨-intro₁ g = ∨-intro₁ (fst x , g)

-- proof of below propositions implie each other.

-- excluded middle
em = ∀ {A : Set} → A ∨ ¬ A

-- double negation elimination
dne = ∀ {A : Set} → ¬ (¬ A) → A

-- Peirce's law
peirce = ∀ {A B : Set} → ((A → B) → A) → A

-- implication as disconjunction
iad = ∀ {A  B : Set} → (A → B) → ¬ A ∨ B

-- De Morgan
dem = ∀ {A B : Set} → ¬ (¬ A ∨ ¬ B) → A ∨ B

em-dne' : ∀ {A : Set} → (A ∨ ¬ A) → (¬ (¬ A) → A)
em-dne' x y with x
em-dne' x y | ∨-introₒ a = a
em-dne' x y | ∨-intro₁ na = ⊥-elim (y na)

-- understanding path here
em-dne : em → dne
em-dne x y with x
em-dne x y | ∨-introₒ a = a
em-dne x y | ∨-intro₁ na = ⊥-elim (y na)