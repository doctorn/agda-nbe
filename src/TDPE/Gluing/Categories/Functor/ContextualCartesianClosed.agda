{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Functor.ContextualCartesianClosed
  {o o′ ℓ ℓ′ e e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  where

open import Level
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Categories.Functor.ContextualCartesian
open import Categories.Functor
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module _
  {a} (𝒰 : Set a)
  (𝒞-CCC : ContextualCartesianClosed 𝒞 𝒰)
  (𝒟-CCC : ContextualCartesianClosed 𝒟 𝒰)
  where

  open import TDPE.Gluing.Contexts 𝒰 using (𝒰ᵀ) renaming (_⇒_ to _^_)

  private
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module 𝒞-CCC = ContextualCartesianClosed 𝒞-CCC
    module 𝒟-CCC = ContextualCartesianClosed 𝒟-CCC

  open import TDPE.Gluing.Transport 𝒟

  record CCCFunctor (F : Functor 𝒞 𝒟) : Set (a ⊔ levelOfTerm F) where
    module F = Functor F

    field
      cartesian : CCFunctor 𝒰ᵀ 𝒞-CCC.cartesian 𝒟-CCC.cartesian F

    open CCFunctor cartesian public

    field
      Λ-preserving : ∀ {Γ A B}
                     → (h : (Γ 𝒞-CCC.· A) 𝒞.⇒ (𝒞-CCC.[ B ]))
                     → F.₁ (𝒞-CCC.Λ h)
                         𝒟.≈ transport′ PE.refl []-preserving
                           (𝒟-CCC.Λ (transport ·-preserving []-preserving (F.₁ h)))

      eval-preserving : ∀ {A B}
                        → F.₁ (𝒞-CCC.eval {A} {B})
                            𝒟.≈ transport′
                                  (PE.trans ·-preserving (PE.cong (𝒟-CCC._· A) []-preserving))
                                  []-preserving (𝒟-CCC.eval {A} {B})
