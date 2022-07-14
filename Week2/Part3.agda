{-# OPTIONS --safe --without-K --show-implicit #-}

open import Base
open import Part1

is-decidable : Set → Set
is-decidable A = A + (¬ A)

has-decidable-equality : Set → Set
has-decidable-equality X = (x y : X) → is-decidable (x ≡ y)

has-bool-dec-fct : Set → Set
has-bool-dec-fct A = Σ {A → A → 𝟚} (λ (f : A → A → 𝟚) → (a₁ : A) → (a₂ : A) → (a₁ ≡ a₂ ⇔ (f a₁ a₂) ≡ ⊤))

decidable-equality-char : (A : Set) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A = g , f
  where
    eq : {A : Set} → A → A → 𝟚
    eq {A} a b = {!!}

    f : (x
           : Σ {(x₁ x₂ : A) → 𝟚}
             (λ z →
                (x₁ x₂ : A) →
                Σ {(x₃ : _≡_ {A} x₁ x₂) → _≡_ {𝟚} (z x₁ x₂) ⊤}
                (λ _ → (x₃ : _≡_ {𝟚} (z x₁ x₂) ⊤) → _≡_ {A} x₁ x₂)))
          (x₁ x₂ : A) →
          _≡_ {A} x₁ x₂ + ((x₃ : _≡_ {A} x₁ x₂) → ∅)
    f x x₁ x₂ = {!!}

    g : (x : (x₁ x₂ : A) → _≡_ {A} x₁ x₂ + ((x₃ : _≡_ {A} x₁ x₂) → ∅)) →
          Σ {(x₁ x₂ : A) → 𝟚}
          (λ z →
             (x₁ x₂ : A) →
             Σ {(x₃ : _≡_ {A} x₁ x₂) → _≡_ {𝟚} (z x₁ x₂) ⊤}
             (λ _ → (x₃ : _≡_ {𝟚} (z x₁ x₂) ⊤) → _≡_ {A} x₁ x₂))
    g x = (λ x₁ x₂ → eq x₁ x₂) , (λ x₁ x₂ → (λ x₃ → refl ⊤) , {!!})
