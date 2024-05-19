{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Contexts {a} (𝒰 : Set a) where

data 𝒰ᵀ : Set a where
  `_` : 𝒰 → 𝒰ᵀ
  _⇒_ : 𝒰ᵀ → 𝒰ᵀ → 𝒰ᵀ

infixl 5 _·_

data ℭ : Set a where
  𝟙 : ℭ
  _·_ : ℭ → 𝒰ᵀ → ℭ

⟦_⟧ᵀ : ∀ {b} {A : Set b} → 𝒰ᵀ → (𝒰 → A) → (A → A → A) → A
⟦ ` A ` ⟧ᵀ η μ = η A
⟦ A ⇒ B ⟧ᵀ η μ = μ (⟦ A ⟧ᵀ η μ ) (⟦ B ⟧ᵀ η μ)

⟦_⟧ᶜ : ∀ {b c} {A : Set b} {B : Set c}
       → ℭ
       → (𝒰 → A)     -- base types
       → (A → A → A) -- exponentials
       → B           -- empty
       → (B → A → B) -- extensions
       → B
⟦ 𝟙     ⟧ᶜ η μ 𝟘 _⊕_ = 𝟘
⟦ Γ · A ⟧ᶜ η μ 𝟘 _⊕_ = ⟦ Γ ⟧ᶜ η μ 𝟘 _⊕_ ⊕ ⟦ A ⟧ᵀ η μ
