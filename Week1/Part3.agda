{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Base
open import Part1
open import Part2

-- Exercise 1
||-is-commutative : (a b : Bool) → (a || b) ≡ (b || a)
||-is-commutative true true = refl true
||-is-commutative true false = refl true
||-is-commutative false true = refl true
||-is-commutative false false = refl false

-- Exercise 2
&&-is-commutative : (a b : Bool) → (a && b) ≡ (b && a)
&&-is-commutative true true = refl true
&&-is-commutative true false = refl false
&&-is-commutative false true = refl false
&&-is-commutative false false = refl false

-- Exercise 3
&&-is-associative : (a b c : Bool) → (a && (b && c)) ≡ ((a && b) && c)
&&-is-associative true true true = refl true
&&-is-associative true true false = refl false
&&-is-associative true false true = refl false
&&-is-associative true false false = refl false
&&-is-associative false true true = refl false
&&-is-associative false true false = refl false
&&-is-associative false false true = refl false
&&-is-associative false false false = refl false

-- Exercise 4
max-is-commutative : (n m : ℕ) → (max n m) ≡ (max m n)
max-is-commutative zero zero = refl zero
max-is-commutative zero (succ b) = refl (succ b)
max-is-commutative (succ a) zero = refl (succ a)
max-is-commutative (succ a) (succ b) = to-show
  where
    IH : max a b ≡ max b a
    IH = max-is-commutative a b
    to-show : succ (max a b) ≡ succ (max b a)
    to-show = ap succ IH

min-is-commutative : (n m : ℕ) → (min n m) ≡ (min m n)
min-is-commutative zero zero = refl zero
min-is-commutative zero (succ m) = refl zero
min-is-commutative (succ n) zero = refl zero
min-is-commutative (succ n) (succ m) = to-show
  where
    IH : (min n m) ≡ (min m n)
    IH = min-is-commutative n m
    to-show : (min (succ n) (succ m)) ≡ (min (succ m) (succ n))
    to-show = ap succ IH

-- Exercise 5
0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero = refl zero
0-right-neutral (succ n) = to-show
  where
    IH : n ≡ (n + 0)
    IH = 0-right-neutral n
    to-show : (succ n) ≡ (succ (n + 0))
    to-show = ap succ IH

-- Exercise 6
_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g (f x)

concat-refl : {X : Set} → (x y : X) → (xs ys : List X) → (x ≡ y) → (xs ≡ ys) → ((x :: xs) ≡ (y :: ys))
concat-refl {X} x .x xs .xs (refl .x) (refl .xs) = refl (x :: xs)

map-id : {X : Set} → (xs : List X) → map id xs ≡ xs
map-id [] = refl []
map-id (x :: x₁) = to-show
  where
    IH : map id x₁ ≡ x₁
    IH = map-id x₁
    to-show : id x :: map id x₁ ≡ x :: x₁
    to-show = concat-refl (id x) (x) (map id x₁) (x₁) (refl x) IH

map-comp : {X Y Z : Set} → (f : X → Y) → (g : Y → Z) → (xs : List X) → ((map (g ∘ f) xs) ≡ (map g (map f xs)))
map-comp f g [] = refl []
map-comp f g (x :: xs) = to-show
  where
    IH : map (g ∘ f) xs ≡ map g (map f xs)
    IH = map-comp f g xs
    to-show : g (f x) :: map (g ∘ f) xs ≡ g (f x) :: map g (map f xs)
    to-show = concat-refl (g (f x)) (g (f x)) (map (g ∘ f) xs) (map g (map f xs)) (refl (g (f x))) IH
