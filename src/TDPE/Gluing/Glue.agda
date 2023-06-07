{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

{-
open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Construction.Functors
open import Categories.Yoneda

open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ⟦_⟧)
open import TDPE.Gluing.Syntax 𝒰 using (𝕋𝕞; 𝕋𝕞-CC; !; !η)

open import Data.Product using (_,_)
open import Data.Unit.Polymorphic

open import Relation.Binary using (IsEquivalence; Setoid)

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
                 ; identity = {!!}
                 ; homomorphism = {!!}
                 ; F-resp-≈ = {!!}
                 }

i : Functor 𝕎 𝕋𝕞
i = ⟦_⟧ 𝕋𝕞-CC

Tm : Functor 𝕋𝕞 (Presheaves 𝕎)
Tm = precompose (Functor.op i) ∘F Yoneda.embed 𝕋𝕞

Gl : Category (suc a) a a
Gl = Comma {A = Presheaves 𝕎} Categories.Functor.id Tm

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Categories.Category.ContextualCartesian Gl
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed Gl

-- CC : ContextualCartesian (Lift (suc a) 𝒰)
-- CC = {!!}
-}
