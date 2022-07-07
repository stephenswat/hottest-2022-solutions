{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Base

-- Exercise 1
_&&_ : Bool → Bool → Bool
true && true = true
true && false = false
false && true = false
false && false = false

-- Exercise 2
_^^_ : Bool → Bool → Bool
true ^^ true = false
true ^^ false = true
false ^^ true = true
false ^^ false = false

-- Exercise 3
_^_ : ℕ → ℕ → ℕ
a ^ zero = 1
a ^ succ b = a * (a ^ b)

^-example : (3 ^ 4) ≡ 81
^-example = refl 81

_! : ℕ → ℕ
zero ! = 1
succ a ! = (succ a) * (a !)

!-example : (4 !) ≡ 24
!-example = refl 24

-- Exercise 4
max : ℕ → ℕ → ℕ
max zero zero = zero
max zero (succ b) = succ b
max (succ a) zero = succ a
max (succ a) (succ b) = succ (max a b)

min : ℕ → ℕ → ℕ
min zero zero = zero
min zero (succ b) = zero
min (succ a) zero = zero
min (succ a) (succ b) = succ (min a b)

min-example : min 5 3 ≡ 3
min-example = refl 3

-- Exercise 5
map : {X Y : Set} → (X → Y) → List X → List Y
map {X} {Y} f [] = []
map {X} {Y} f (x :: x₁) = (f x) :: (map f x₁)

map-example : (map (_+ 3) (1 :: 2 :: 3 :: [])) ≡ (4 :: 5 :: 6 :: [])
map-example = refl _

if_then_else_ : {X : Set} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

-- Exercise 6
filter : {X : Set} → (p : X → Bool) → List X → List X
filter p [] = []
filter p (x :: x₁) = if p x then (x :: (filter p x₁)) else (filter p x₁)

is-non-zero : ℕ → Bool
is-non-zero zero    = false
is-non-zero (succ _) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl _
