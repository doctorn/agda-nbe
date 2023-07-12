{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.CartesianClosed {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)

open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Glue.Cartesian 𝒰
open import TDPE.Gluing.Glue.Lambda 𝒰
open import TDPE.Gluing.Glue.Eval 𝒰 using (eval; eval′)
open import TDPE.Gluing.Glue.Yoga 𝒰 using (ϕ; ψ)

open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ)
open import TDPE.Gluing.Contexts 𝒰 using (𝒰ᵀ) renaming (_⇒_ to _^_)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh
import TDPE.Gluing.Syntax 𝒰 as Syntax

open import Categories.Diagram.Pullback Psh.Psh using (Pullback)

module 𝕎 = Category 𝕎
open ContextualCartesian CC

{-
module _ {Γ A B} (f : Γ · A Gl.⇒ [ B ]) where

  private
    Λ′f = Λ′′ {Γ} {A} {B} f

    module Γα = Functor (CommaObj.α Γ)
    module fg = NaturalTransformation (Comma⇒.g f)
    module Λ′f = NaturalTransformation Λ′f

  β′ : eval′ Psh.∘ Psh.⟨ (Psh.unit Psh.∘ Λ′f) Psh.∘ Psh.π , Psh.𝓏 ⟩ Psh.≈ Comma⇒.g f
  β′ {Δ} {γ , a} {δ , b} (γ≈δ , a≈b) = begin
      tt , proj₂ (fg.η Δ ⟨$⟩ (Γα.₁ ϵ ⟨$⟩ γ , a))
    ≈⟨ tt , (proj₂ (cong (fg.η Δ) ((Γα.identity γ≈δ) , a≈b))) ⟩
      tt , proj₂ (fg.η Δ ⟨$⟩ (δ , b))
    ≈⟨ tt , proj₂ (Setoid.refl [B]) ⟩
      fg.η Δ ⟨$⟩ (δ , b)
    ∎
    where [B] = Functor.₀ (CommaObj.α [ B ]) Δ
          open Reasoning [B]

  β : eval Gl.∘ ⟨ (Λ′ {Γ} {A} {B} f) Gl.∘ (π {Γ} {A}) , 𝓏 {Γ} {A} ⟩ Gl.≈ f
  β = β′ , ContextualCartesianClosed.β Syntax.CCC (Comma⇒.h f)
-}

module _
  {Γ A B}
  {g : Γ · A Gl.⇒ [ B ]}
  {h : Γ Gl.⇒ [ A ^ B ]}
  (p : eval Gl.∘ ⟨ h Gl.∘ π {Γ} {A} , 𝓏 {Γ} {A} ⟩ Gl.≈ g)
  where

  private
    Λ′g = Λ′′ {Γ} {A} {B} g

  unique′ : Comma⇒.g h Psh.≈ Psh.unit Psh.∘ Λ′g
  unique′ {Δ} {γ} {δ} γ≈δ = begin
      NaturalTransformation.η (Comma⇒.g h) Δ ⟨$⟩ γ
    ≈⟨ tt , proj₂ (Setoid.refl [A^B]) ⟩
      tt , proj₂ (NaturalTransformation.η (Comma⇒.g h) Δ ⟨$⟩ γ)
    ≈⟨
        tt
      ,
        Pullback.unique
          (ψ {A} {B} Psh.⊗ ϕ {A} {B})
          {h₁ = h₁ {Γ} {A} {B} g}
          {h₂ = h₂ {Γ} {A} {B} g}
          {i = Psh.counit Psh.∘ Comma⇒.g h}
          {eq = coherence {Γ} {A} {B} g}
          (λ {Δ} {γ} {δ} γ≈δ → {!!})
          (λ {Δ} {x} {y} x≈y {Ξ} {z} {w} z≈w → {!!})
          γ≈δ
    ⟩
      tt , NaturalTransformation.η (Λ′g) Δ ⟨$⟩ δ
    ∎
    where [A^B] = Functor.₀ (CommaObj.α [ A ^ B ]) Δ
          open Reasoning [A^B]

{-
  unique : h Gl.≈ Λ′ {Γ} {A} {B} g
  unique = unique′ , ContextualCartesianClosed.unique Syntax.CCC (proj₂ p)

CCC : ContextualCartesianClosed Gl 𝒰
CCC = record
  { cartesian = CC
  ; Λ = Λ′
  ; eval = eval
  ; β = λ {Γ} {A} {B} f → β {Γ} {A} {B} f
  ; unique = λ {Γ} {A} {B} {g} {h} p → unique {Γ} {A} {B} {g} {h} p
  }
-}
