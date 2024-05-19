{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module NbE.Gluing.Categories.Functor.ContextualCartesian
  {o o′ ℓ ℓ′ e e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  where

open import Level
open import NbE.Gluing.Categories.Category.ContextualCartesian
open import Categories.Functor
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module _
  {a} (𝒰 : Set a)
  (𝒞-CC : ContextualCartesian 𝒞 𝒰)
  (𝒟-CC : ContextualCartesian 𝒟 𝒰)
  (F : Functor 𝒞 𝒟)
  where

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module 𝒞-CC = ContextualCartesian 𝒞-CC
    module 𝒟-CC = ContextualCartesian 𝒟-CC
    module F = Functor F

  open import NbE.Gluing.Transport 𝒟

  record CCFunctor : Set (a ⊔ levelOfTerm F) where

    field
      terminal-preserving : F.₀ 𝒞-CC.⊤ ≡ 𝒟-CC.⊤
      ·-preserving : ∀ {Γ A} → F.₀ (Γ 𝒞-CC.· A) ≡ F.₀ Γ 𝒟-CC.· A

    []-preserving : ∀ {A} → F.₀ 𝒞-CC.[ A ] ≡ 𝒟-CC.[ A ]
    []-preserving {A} = PE.trans ·-preserving (PE.cong (𝒟-CC._· A) terminal-preserving)

    field
      π-preserving : ∀ {Γ A}
                     → F.₁ (𝒞-CC.π {Γ} {A})
                         𝒟.≈ transport′ ·-preserving PE.refl (𝒟-CC.π {F.₀ Γ} {A})
      𝓏-preserving : ∀ {Γ A}
                     → F.₁ (𝒞-CC.𝓏 {Γ} {A})
                         𝒟.≈ transport′ ·-preserving []-preserving (𝒟-CC.𝓏 {F.₀ Γ} {A})
