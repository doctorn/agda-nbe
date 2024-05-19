{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module NbE.Gluing.Categories.Category.ContextualCartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Categories.Object.Terminal 𝒞 using (Terminal)
open import Categories.Object.Product 𝒞 using (IsProduct; IsProduct⇒Product; Product; up-to-iso)
open Category 𝒞

open import Categories.Morphism 𝒞

record ContextualCartesian {a} (𝒰 : Set a) : Set (a ⊔ levelOfTerm 𝒞) where
  infixl 5 _·_

  field
    terminal : Terminal
    _·_ : Obj → 𝒰 → Obj

  module Term = Terminal terminal
  open Term using (⊤; !; !-unique) public

  [_] : 𝒰 → Obj
  [ A ] = ⊤ · A

  field
    π : ∀ {Γ A} → Γ · A ⇒ Γ
    𝓏 : ∀ {Γ A} → Γ · A ⇒ [ A ]

    extensions : ∀ {Γ A} → IsProduct (π {Γ} {A}) (𝓏 {Γ} {A})

    𝓏-id : ∀ {A} → 𝓏 {⊤} {A} ≈ id

  module _ {Γ A} where
    ext = IsProduct⇒Product (extensions {Γ} {A})

    module Ext = Product ext
    open Ext using (⟨_,_⟩) public

  ⟨!,_⟩-id : ∀ {Γ A} (f : Γ ⇒ [ A ]) → ⟨ ! , f ⟩ ≈ f
  ⟨!,_⟩-id f = Ext.unique (Equiv.sym (!-unique _)) (Equiv.trans (∘-resp-≈ˡ 𝓏-id) identityˡ)
