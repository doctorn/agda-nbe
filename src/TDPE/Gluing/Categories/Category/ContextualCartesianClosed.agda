{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Category.ContextualCartesianClosed {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import TDPE.Gluing.Categories.Category.ContextualCartesian 𝒞 using (ContextualCartesian)
open Category 𝒞

record ContextualCartesianClosed (𝒰 : Set o) : Set (levelOfTerm 𝒞) where
  infixr 9 _^_

  field
    cartesian : ContextualCartesian 𝒰

  open ContextualCartesian cartesian

  field
    _^_ : 𝒰 → 𝒰 → 𝒰

    Λ : ∀ {Γ A B} → Γ · A ⇒ [ B ] → Γ ⇒ [ B ^ A ]

    _⦅_⦆ : ∀ {Γ A B} → Γ ⇒ [ B ^ A ] → Γ ⇒ [ A ] → Γ ⇒ [ B ]

    β : ∀ {Γ A B} (f : Γ · A ⇒ [ B ]) (x : Γ ⇒ [ A ])
        → (Λ f) ⦅ x ⦆ ≈ f ∘ ⟨ id , x ⟩
    η : ∀ {Γ A B} (f : Γ ⇒ [ B ^ A ])
        → f ≈ Λ ((f ∘ π) ⦅ 𝓏 ⦆)
