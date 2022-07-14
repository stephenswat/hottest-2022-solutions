{-# OPTIONS --safe --without-K --show-implicit #-}

open import Base

-- Exercise 1
uncurry : {A B X : Set} → (A → B → X) → (A × B → X)
uncurry {A} {B} f = λ ((a , b) : (A × B)) → f a b

curry : {A B X : Set} → (A × B → X) → (A → B → X)
curry {A} {B} f = λ (a : A) → λ (b : B) → f (a , b)

-- Exercise 2
[i] : {A B C : Set} → (A × B) + C → (A + C) × (B + C)
[i] (inl (π₁ , π₂)) = (inl π₁) , (inl π₂)
[i] (inr x) = (inr x) , (inr x)


[ii] : {A B C : Set} → (A × B) + C → (A + C) × (B + C)
[ii] = [i]

[iii] : {A B : Set} → ¬ (A + B) → (¬ A) × (¬ B)
[iii] p = (λ x → p (inl x)) , (λ x → p (inr x))

-- Unprovable
-- [iv] : {A B : Set} → ¬ (A × B) → (¬ A) + (¬ B)

[v] : {A B : Set} → (A → B) → (¬ B) → (¬ A)
[v] f v = v ∘ f

-- Unprovable
--[vi] : {A B : Set} → ((¬ A) → (¬ B)) → B → A

-- Unprovable
-- [vii] : {A B : Set} → ((A → B) → A) → A
  
[viii] : {A : Set} {B : A → Set} → ¬ (Σ {A} B) → (a : A) → (¬ (B a))
[viii] p v = λ z → p (v , z)

-- Unprovable
-- [ix] : {A : Set} {B : A → Set} → ¬ ((a : A) → B a) → (Σ {A} (λ a → ¬ (B a)))

[x] : {A B : Set} {C : A → B → Set}
    → ((a : A) → (Σ {B} (λ b → C a b)))
    → Σ {A → B} (λ f → (a : A) → C a (f a))
[x] {A} p = (λ (a : A) → π₁ (p a)) , (λ (a : A) → π₂ (p a))


-- Exercise 3
¬¬_ : Set → Set
¬¬ A = ¬ (¬ A)

¬¬¬_ : Set → Set
¬¬¬ A = ¬ (¬¬ A)

tne : {A : Set} → (¬¬¬ A) → (¬ A)
tne p = λ a → p (λ b → b a)


-- Exercise 4
¬¬-functor : {A B : Set} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor p a = λ f → a (f ∘ p)

¬¬-kleisli : {A B : Set} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli p a = λ f → a (λ g → (p g) f)

