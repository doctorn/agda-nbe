{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.CartesianClosed {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)

open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as PE
import Relation.Binary.Reasoning.Setoid as Reasoning

open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Glue.Cartesian 𝒰
open import TDPE.Gluing.Glue.Lambda 𝒰
open import TDPE.Gluing.Glue.Eval 𝒰 using (eval; eval′)
open import TDPE.Gluing.Glue.Yoga 𝒰 using (↓₀; ↑₀; ϕ; ψ; 𝓡₀; yoga₀)

open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁)
open import TDPE.Gluing.Embedding 𝒰
open import TDPE.Gluing.Contexts 𝒰 using (ℭ; 𝒰ᵀ) renaming (_⇒_ to _^_)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
import TDPE.Gluing.Representation 𝒰 as R
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)

open import Categories.Diagram.Pullback Psh.Psh using (Pullback)

module 𝕎 = Category 𝕎
module CC = ContextualCartesian CC

module _ {Γ A B} (f : Γ CC.· A Gl.⇒ CC.[ B ]) where

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
    where [B] = Functor.₀ (CommaObj.α CC.[ B ]) Δ
          open Reasoning [B]

  β : eval Gl.∘ CC.⟨ (Λ′ {Γ} {A} {B} f) Gl.∘ (CC.π {Γ} {A}) , CC.𝓏 {Γ} {A} ⟩ Gl.≈ f
  β = β′ , ContextualCartesianClosed.β Syntax.CCC (Comma⇒.h f)

module _
  {Γ A B}
  {g : Γ CC.· A Gl.⇒ CC.[ B ]}
  {h : Γ Gl.⇒ CC.[ A ^ B ]}
  (eq : eval Gl.∘ CC.⟨ h Gl.∘ CC.π {Γ} {A} , CC.𝓏 {Γ} {A} ⟩ Gl.≈ g)
  where

  private
    Λ′g = Λ′′ {Γ} {A} {B} g

    module ψ⊗ϕ = Pullback (ψ {A} {B} Psh.⊗ ϕ {A} {B})

    triangle₁ : ψ⊗ϕ.p₁ Psh.∘ Psh.counit Psh.∘ Comma⇒.g h Psh.≈ h₁ {Γ} {A} {B} g
    triangle₁ {Δ} {γ} {δ} γ≈δ =
      let (tt , ((hg₁ , hg₂) , commutes)) = hg.η Δ ⟨$⟩ γ in (begin
        hg₁
      ≈⟨ S.sym 𝓏η ⟩
        ! ∷ 𝓏 [ hg₁ ]
      ≈⟨ ∷-congᵣ Λη ⟩
        ! ∷ Λ ((𝓏 [ hg₁ ] [ π id ]) ⦅ 𝓏 ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (app-cong₂ sb-assoc (𝒵-cong (S.sym (yoga₀ PE.refl))))) ⟩
        ! ∷ Λ ((𝓏 [ hg₁ ∘ π id ]) ⦅ 𝒵 (𝔦₀.η A (Δ ℭ.· A) ⟨$⟩ (↓₀.η A (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏))) ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (app-congₗ (sb-congᵣ (∘-congᵣ (π-cong (S.sym E.identity)))))) ⟩
        ! ∷ Λ ((𝓏 [ hg₁ ∘ (π (E.₁ (ϵ {Δ}))) ]) ⦅ 𝒵 (𝔦₀.η A (Δ ℭ.· A) ⟨$⟩ (↓₀.η A (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏))) ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (𝒵-cong (commutes (Setoid.refl (𝓡₀.₀ A (Δ ℭ.· A)) , PE.refl {x = ω₁ ϵ})))) ⟩
        ! ∷ Λ (𝒵 (𝔦₀.η B (Δ ℭ.· A) ⟨$⟩ (↓₀.η B (Δ ℭ.· A) ⟨$⟩ (NaturalTransformation.η hg₂ (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ (ϵ 𝕎.∘ ϵ))))))
      ≈⟨ ∷-congᵣ (Λ-cong (𝒵-cong (cong (𝔦₀.η B (Δ ℭ.· A)) (cong (↓₀.η B (Δ ℭ.· A)) (cong (NaturalTransformation.η hg₂ (Δ ℭ.· A)) (Setoid.refl ( (𝓡₀.₀ A (Δ ℭ.· A))) , (PE.cong ω₁ 𝕎.identity²))))))) ⟩
        ! ∷ Λ (𝒵 (𝔦₀.η B (Δ ℭ.· A) ⟨$⟩ (↓₀.η B (Δ ℭ.· A) ⟨$⟩ (NaturalTransformation.η hg₂ (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ (ϵ {Δ}))))))
      ≈⟨ ∷-congᵣ (Λη {f =  Λ (𝒵 (𝔦₀.η B (Δ ℭ.· A) ⟨$⟩ (↓₀.η B (Δ ℭ.· A) ⟨$⟩ (NaturalTransformation.η hg₂ (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ)))))}) ⟩
        ! ∷ Λ ((Λ (𝒵 (𝔦₀.η B (Δ ℭ.· A) ⟨$⟩ (↓₀.η B (Δ ℭ.· A) ⟨$⟩ (NaturalTransformation.η hg₂ (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ))))) [ π id ]) ⦅ 𝓏 ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (app-congₗ (C.sym v𝓏))) ⟩
        ! ∷ Λ ((𝓏 [ ! ∷ (Λ (𝒵 (𝔦₀.η B (Δ ℭ.· A) ⟨$⟩ (↓₀.η B (Δ ℭ.· A) ⟨$⟩ (NaturalTransformation.η hg₂ (Δ ℭ.· A) ⟨$⟩ (↑₀.η A (Δ ℭ.· A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ))))) [ π id ]) ]) ⦅ 𝓏 ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (app-congₗ (sb-congᵣ (∘-congₗ (S.sym (Comma⇒.commute h (Setoid.sym (Γα.₀ Δ) γ≈δ))))))) ⟩
        ! ∷ Λ ((𝓏 [ (Comma⇒.h h ∘ (Γf.η Δ ⟨$⟩ δ)) ∘ π id ]) ⦅ 𝓏 ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (app-congₗ (sb-congᵣ (S.trans (S.trans ∘-assoc (∘-congᵣ π-id)) (S.trans (∘-congᵣ (S.sym πβ′)) ∘-sym-assoc))))) ⟩
        ! ∷ Λ ((𝓏 [ (Comma⇒.h h ∘ π id) ∘ (π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏) ]) ⦅ 𝓏 ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (app-cong₂ (C.sym sb-assoc) (C.sym v𝓏))) ⟩
        ! ∷ Λ ((𝓏 [ Comma⇒.h h ∘ π id ] [ π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏 ]) ⦅ 𝓏 [ π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏 ] ⦆)
      ≈⟨ ∷-congᵣ (Λ-cong (C.sym sb-app)) ⟩
        ! ∷ Λ (((𝓏 [ Comma⇒.h h ∘ π id ]) ⦅ 𝓏 ⦆) [ π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏 ])
      ≈⟨ ∷-congᵣ (Λ-cong (sb-congₗ (app-cong₂ (C.sym vp) (C.sym v𝓏)))) ⟩
        ! ∷ Λ (((p 𝓏 [ Comma⇒.h h ∘ π id ∷ 𝓏 ]) ⦅ 𝓏 [ Comma⇒.h h ∘ π id ∷ 𝓏 ] ⦆) [ π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏 ])
      ≈⟨ ∷-congᵣ (Λ-cong (sb-congₗ (C.sym sb-app))) ⟩
        ! ∷ Λ ((p 𝓏 ⦅ 𝓏 ⦆) [ Comma⇒.h h ∘ π id ∷ 𝓏 ] [ π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏 ])
      ≈⟨ ∷-congᵣ (Λ-cong (𝒵-cong (∘-congₗ (proj₂ eq)))) ⟩
        ! ∷ Λ (𝒵 (Comma⇒.h g ∘ (π (Γf.η Δ ⟨$⟩ δ) ∷ 𝓏)))
      ∎)
      where open Reasoning S.setoid

            module hg = NaturalTransformation (Comma⇒.g h)
            module Γα = Functor (CommaObj.α Γ)
            module Γf = NaturalTransformation (CommaObj.f Γ)

    triangle₂ : ψ⊗ϕ.p₂ Psh.∘ Psh.counit Psh.∘ Comma⇒.g h Psh.≈ h₂ {Γ} {A} {B} g
    triangle₂ {Δ} {γ} {δ} γ≈δ {Ξ} {a₁ , w} {a₂ , _} (a₁≈a₂ , PE.refl) =
      let (tt , ((_ , hgΔγ) , _)) = hg.η Δ ⟨$⟩ γ in
      let (tt , ((_ , hgΞwδ) , _)) = hg.η Ξ ⟨$⟩ (Γα.₁ w ⟨$⟩ δ) in (begin
        NaturalTransformation.η hgΔγ Ξ ⟨$⟩ (a₁ , w)
      ≈⟨ cong (NaturalTransformation.η hgΔγ Ξ) (Setoid.refl (𝓡₀.₀ A Ξ) , PE.sym 𝕎.identityʳ) ⟩
        NaturalTransformation.η hgΔγ Ξ ⟨$⟩ (a₁ , w 𝕎.∘ ϵ)
      ≈⟨ proj₂ (proj₁ (proj₂ (hg.sym-commute w γ≈δ))) (Setoid.refl (𝓡₀.₀ A Ξ) , PE.refl) ⟩
        NaturalTransformation.η hgΞwδ Ξ ⟨$⟩ (a₁ , ϵ)
      ≈⟨ proj₂ ((proj₁ eq) (Setoid.refl (Γα.₀ Ξ) , a₁≈a₂)) ⟩
        proj₂ (gg.η Ξ ⟨$⟩ (Γα.₁ w ⟨$⟩ δ , a₂))
      ∎)
      where open Reasoning (𝓡₀.₀ B Ξ)

            module gg = NaturalTransformation (Comma⇒.g g)
            module hg = NaturalTransformation (Comma⇒.g h)
            module Γα = Functor (CommaObj.α Γ)
            module Γf = NaturalTransformation (CommaObj.f Γ)

  unique′ : Comma⇒.g h Psh.≈ Psh.unit Psh.∘ Λ′g
  unique′ {Δ} {γ} {δ} γ≈δ = begin
      NaturalTransformation.η (Comma⇒.g h) Δ ⟨$⟩ γ
    ≈⟨ tt , proj₂ (Setoid.refl [A^B]) ⟩
      tt , proj₂ (NaturalTransformation.η (Comma⇒.g h) Δ ⟨$⟩ γ)
    ≈⟨
        tt
      ,
        ψ⊗ϕ.unique
          {h₁ = h₁ {Γ} {A} {B} g}
          {h₂ = h₂ {Γ} {A} {B} g}
          {i = Psh.counit Psh.∘ Comma⇒.g h}
          {eq = coherence {Γ} {A} {B} g}
          triangle₁
          triangle₂
          γ≈δ
    ⟩
      tt , NaturalTransformation.η Λ′g Δ ⟨$⟩ δ
    ∎
    where [A^B] = Functor.₀ (CommaObj.α CC.[ A ^ B ]) Δ
          open Reasoning [A^B]

  unique : h Gl.≈ Λ′ {Γ} {A} {B} g
  unique = unique′ , ContextualCartesianClosed.unique Syntax.CCC (proj₂ eq)

CCC : ContextualCartesianClosed Gl 𝒰
CCC = record
  { cartesian = CC
  ; Λ = Λ′
  ; eval = eval
  ; β = λ {Γ} {A} {B} f → β {Γ} {A} {B} f
  ; unique = λ {Γ} {A} {B} {g} {h} eq → unique {Γ} {A} {B} {g} {h} eq
  }
