{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Category.ContextualCartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Categories.Object.Terminal 𝒞 using (Terminal)
open import Categories.Object.Product 𝒞 using (IsProduct; IsProduct⇒Product; Product)
open Category 𝒞

record ContextualCartesian (𝒰 : Set o) : Set (levelOfTerm 𝒞) where
  infixl 5 _·_

  field
    terminal : Terminal
    _·_ : Obj → 𝒰 → Obj

  [_] : 𝒰 → Obj
  [ A ] = Terminal.⊤ terminal · A

  field
    π : ∀ {Γ A} → Γ · A ⇒ Γ
    𝓏 : ∀ {Γ A} → Γ · A ⇒ [ A ]

    extensions : ∀ {Γ A} → IsProduct (π {Γ} {A}) (𝓏 {Γ} {A})

  module Term = Terminal terminal

  module _ {Γ A} where
    module Ext = Product (IsProduct⇒Product (extensions {Γ} {A}))

    open Ext using (⟨_,_⟩) public
