{-# OPTIONS --safe --without-K --show-implicit #-}

data 𝟘 : Set where

data 𝟙 : Set where
  ⋆ : 𝟙

data 𝟚 : Set where
  ⊤ : 𝟚
  ⊥ : 𝟚

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

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → (a ≡ a)

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)

infix -2 _⇔_
