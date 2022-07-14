{-# OPTIONS --safe --without-K --show-implicit #-}

open import Base

-- Exercise 1
bool-as-type : 𝟚 → Set
bool-as-type ⊤ = 𝟙
bool-as-type ⊥ = 𝟘

-- Exercise 2
id : {A : Set} → A → A
id x = x

bool-≡-char₁ : ∀ (b₁ b₂ : 𝟚) → b₁ ≡ b₂ → (bool-as-type b₁ ⇔ bool-as-type b₂)
bool-≡-char₁ ⊤ ⊤ p = id , id
bool-≡-char₁ ⊥ ⊥ p = id , id

-- Exercise 3
true≢false : ¬ (⊤ ≡ ⊥)
true≢false = {!!}

-- Exercise 4
bool-≡-char₂ : ∀ (b₁ b₂ : 𝟚) → (bool-as-type b₁ ⇔ bool-as-type b₂) → b₁ ≡ b₂
bool-≡-char₂ ⊤ ⊤ p = refl ⊤
bool-≡-char₂ ⊤ ⊥ p = {!!}
bool-≡-char₂ ⊥ ⊤ p = {!!}
bool-≡-char₂ ⊥ ⊥ p = refl ⊥
