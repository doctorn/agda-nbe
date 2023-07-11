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

open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh
import TDPE.Gluing.Syntax 𝒰 as Syntax

module 𝕎 = Category 𝕎
open ContextualCartesian CC

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

CCC : ContextualCartesianClosed Gl 𝒰
CCC = record
  { cartesian = CC
  ; Λ = Λ′
  ; eval = eval
  ; β = λ {Γ} {A} {B} f → β {Γ} {A} {B} f
  ; unique = {!!}
  }
