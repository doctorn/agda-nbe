module TDPE.Types where

open import Level

infixl 6 _⊗_
infixr 5 _⇒_

data _ᵀ {ℓ} (𝒰 : Set ℓ) : Set ℓ where
  `_` : 𝒰 → 𝒰 ᵀ
  _⊗_ : 𝒰 ᵀ → 𝒰 ᵀ → 𝒰 ᵀ
  _⇒_ : 𝒰 ᵀ → 𝒰 ᵀ → 𝒰 ᵀ

⟦_⟧ᵀ : ∀ {ℓ ℓ'} {𝒰 : Set ℓ} {𝒟 : Set ℓ'}
      → 𝒰 ᵀ → (B : 𝒰 → 𝒟) → (p : 𝒟 → 𝒟 → 𝒟) → (a : 𝒟 → 𝒟 → 𝒟) → 𝒟
⟦_⟧ᵀ {𝒰 = 𝒰} {𝒟} τ B p a = I τ
  where I : 𝒰 ᵀ → 𝒟
        I ` A `     = B A
        I (τ₁ ⊗ τ₂) = p (I τ₁) (I τ₂)
        I (τ₁ ⇒ τ₂) = a (I τ₁) (I τ₂)
