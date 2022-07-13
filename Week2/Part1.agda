{-# OPTIONS --safe --without-K --show-implicit #-}

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

record Σ {A : Set} (B : A → Set) : Set where
  constructor
    _,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public

Σ-elim : {A : Set} {B : A → Set} {C : Σ (λ x → B x) → Set}
       → ((x : A) (y : B x) → C (x , y))
       → (z : Σ B) → C z
Σ-elim f (x , y) = f x y 

_×_ : Set → Set → Set
A × B = Σ {A} (λ _ → B)

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

data ∅ : Set where

¬_ : Set → Set
¬ A = A → ∅

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

[ix] : {A : Set} {B : A → Set} → ¬ ((a : A) → B a) → (Σ {A} (λ a → ¬ (B a)))
[ix] p = {!!} , {!!}
