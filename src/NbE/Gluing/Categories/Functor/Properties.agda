{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Categories.Functor.Properties where

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.NaturalTransformation using (_∘ʳ_)

module _ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
  {A : Category o₁ ℓ₁ e₁}
  {B : Category o₂ ℓ₂ e₂}
  {C : Category o₃ ℓ₃ e₃}
  (F : Functor A B)
  where

  precompose : Functor (Functors B C) (Functors A C)
  precompose = record
                 { F₀ = λ G → G ∘F F
                 ; F₁ = λ α → α ∘ʳ F
                 ; identity = λ {G} {x} → Category.Equiv.refl C
                 ; homomorphism = λ {X} {Y} {Z} {f} {g} {x} → Category.Equiv.refl C
                 ; F-resp-≈ = λ f≈g {x} → f≈g
                 }
