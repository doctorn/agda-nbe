{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Functor.Instance.Identity
  {o ℓ e} {𝒞 : Category o ℓ e} where

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Categories.Functor using (id) public

open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Categories.Functor.ContextualCartesian {𝒞 = 𝒞} {𝒞}
open import TDPE.Gluing.Categories.Functor.ContextualCartesianClosed {𝒞 = 𝒞} {𝒞}

id-CC : ∀ {a} (𝒰 : Set a) (𝒞-CC : ContextualCartesian 𝒞 𝒰) → CCFunctor 𝒰 𝒞-CC 𝒞-CC id
id-CC _ _ = record
  { terminal-preserving = PE.refl
  ; ·-preserving = PE.refl
  ; π-preserving = λ {Γ} {A} → Category.Equiv.refl 𝒞
  ; 𝓏-preserving = λ {Γ} {A} → Category.Equiv.refl 𝒞
  }

id-CCC : ∀ {a} (𝒰 : Set a) (𝒞-CCC : ContextualCartesianClosed 𝒞 𝒰) → CCCFunctor 𝒰 𝒞-CCC 𝒞-CCC id
id-CCC _ _ = record
  { cartesian = id-CC _ _
  ; Λ-preserving = λ h → Category.Equiv.refl 𝒞
  ; eval-preserving = λ {A} {B} → Category.Equiv.refl 𝒞
  }
