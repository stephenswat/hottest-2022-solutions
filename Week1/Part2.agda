{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Base
open import Part1

-- Exercise 1
_≣_ : Bool → Bool → Set
true ≣ true = 𝟙
true ≣ false = 𝟘
false ≣ true = 𝟘
false ≣ false = 𝟙

-- Exercise 2
Bool-refl : (b : Bool) → b ≣ b
Bool-refl true = ⋆
Bool-refl false = ⋆

-- Exercise 3
≡-to-≣ : (a b : Bool) → a ≡ b → a ≣ b
≡-to-≣ = {!!}

≣-to-≡ : (a b : Bool) → a ≣ b → a ≡ b
≣-to-≡ = {!!}
