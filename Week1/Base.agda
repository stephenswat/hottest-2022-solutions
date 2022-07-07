{-# OPTIONS --without-K --allow-unsolved-metas #-}

data Bool : Set where
  true false : Bool

_||_ : Bool → Bool → Bool
true || true = true
true || false = true
false || true = true
false || false = false

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + b = b
succ a + b = succ (a + b)

_*_ : ℕ → ℕ → ℕ
zero * b = 0
succ a * b = b + (a * b)

data 𝟘 : Set where

data 𝟙 : Set where
  ⋆ : 𝟙

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 10 _::_

data _≡_ {A : Set} : A → A → Set where
 refl : (x : A) → x ≡ x

infix 0 _≡_

ap : {n m : ℕ} → (f : ℕ → ℕ) → (n ≡ m) → (f n ≡ f m)
ap f (refl x) = refl (f x)

id : {A : Set} → A → A
id x = x
