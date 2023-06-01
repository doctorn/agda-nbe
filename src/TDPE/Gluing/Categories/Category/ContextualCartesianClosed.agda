{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Category.ContextualCartesianClosed
  {o ℓ e} (𝒞 : Category o ℓ e) (𝒰 : Set o) where

open import Level

open import TDPE.Gluing.Categories.Category.ContextualCartesian 𝒞 using (ContextualCartesian)
open import TDPE.Gluing.Contexts 𝒰 using (𝒰ᵀ) renaming (_⇒_ to _^_)

open Category 𝒞

record ContextualCartesianClosed : Set (levelOfTerm 𝒞) where
  field
    cartesian : ContextualCartesian (𝒰ᵀ)

  open ContextualCartesian cartesian

  field
    Λ : ∀ {Γ A B} → Γ · A ⇒ [ B ] → Γ ⇒ [ A ^ B ]

    eval : ∀ {A B} → [ A ^ B ] · A ⇒ [ B ]

    β : ∀ {Γ A B} (f : Γ · A ⇒ [ B ])
        → eval ∘ ⟨ Λ f ∘ π , 𝓏 ⟩ ≈ f

    unique : ∀ {Γ A B} {g : (Γ · A) ⇒ [ B ]} {h : Γ ⇒ [ A ^ B ]}
             → eval ∘ ⟨ h ∘ π , 𝓏 ⟩ ≈ g
             → h ≈ Λ g

  η : ∀ {Γ A B} (f : Γ ⇒ [ A ^ B ]) → f ≈ Λ (eval ∘ ⟨ f ∘ π , 𝓏 ⟩)
  η f = unique Equiv.refl

  Λ-cong : ∀ {Γ A B} {f g : Γ · A ⇒ [ B ]} → f ≈ g → Λ f ≈ Λ g
  Λ-cong {f = f} {g} f≈g = unique (Equiv.trans (β f) f≈g)
