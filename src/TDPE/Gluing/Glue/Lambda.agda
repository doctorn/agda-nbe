{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Lambda {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Glue.Cartesian 𝒰 using (CC; ⊤; _×_)
open import TDPE.Gluing.Glue.Yoga 𝒰 using (𝓡₀; ϕ; ψ; ↓₀; ↑₀; yoga₀)
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁; ω₂; 𝒲)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Representation 𝒰 as R using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣)
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

open import Categories.Diagram.Pullback Psh.Psh using (Pullback)

private
  module CC = ContextualCartesian CC
  module 𝕎 = Category 𝕎

module _ {Γ} {A} {B} (f : Γ × A Gl.⇒ (⊤ × B)) where

  private

    module Γf = NaturalTransformation (CommaObj.f Γ)
    module Γα = Functor (CommaObj.α Γ)

    h₁-commute : ∀ {Δ Ξ} (g : 𝒲 Ξ Δ) {γ₁ γ₂} (γ₁≈γ₂ : Setoid._≈_ (Γα.₀ Δ) γ₁ γ₂)
                 → ! ∷ Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ g ⟨$⟩ γ₁)) ∷ 𝓏)))
                   S.≈ ! ∷ 𝓏 [ ! ∷ Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏))) [ W.₁ g ] ]
    h₁-commute {Δ} {Ξ} g {γ₁} {γ₂} γ₁≈γ₂ = ∷-congᵣ (begin
        Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ g ⟨$⟩ γ₁)) ∷ 𝓏)))
      ≈⟨ Λ-cong (𝒵-cong (∘-congᵣ {γ = Comma⇒.h f} (∷-congₗ {a = 𝓏} (π-cong (Γf.commute g γ₁≈γ₂))))) ⟩
        Λ (𝒵 (Comma⇒.h f ∘ (π (id ∘ ((Γf.η Δ ⟨$⟩ γ₂) ∘ W.₁ g)) ∷ 𝓏)))
      ≈⟨ Λ-cong (𝒵-cong (∘-congᵣ {γ = Comma⇒.h f} (∷-congₗ {a = 𝓏} (π-cong ∘-identityˡ)))) ⟩
        Λ (𝒵 (Comma⇒.h f ∘ (π ((Γf.η Δ ⟨$⟩ γ₂) ∘ W.₁ g) ∷ 𝓏)))
      ≈⟨ Λ-cong (C.sym (𝒵-cong (∘-congᵣ {γ = Comma⇒.h f} (∷-cong₂ (S.trans πβ π-lemma) v𝓏)))) ⟩
        Λ (𝒵 (Comma⇒.h f ∘ ((π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏) ∘ (π (W.₁ g) ∷ 𝓏))))
      ≈⟨ Λ-cong (𝒵-cong (∘-sym-assoc {γ = Comma⇒.h f} {δ = π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏} {ζ = π (W.₁ g) ∷ 𝓏})) ⟩
        Λ (𝒵 ((Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏)) ∘ (π (W.₁ g) ∷ 𝓏)))
      ≈⟨ Λ-cong (C.sym (sb-comp {γ = Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏)})) ⟩
        Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏)) [ ↑[ W.₁ g ] ])
      ≈⟨ C.sym sb-lam ⟩
        Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏))) [ W.₁ g ]
      ≈⟨ C.sym v𝓏 ⟩
        𝓏 [ ! ∷ Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₂) ∷ 𝓏))) [ W.₁ g ] ]
      ∎)
      where open Reasoning C.setoid

    h₁ : NaturalTransformation (CommaObj.α Γ) (Tm.₀ (𝟙 · A ⇒ B))
    h₁ = ntHelper (record
      { η = λ Δ → record
        { _⟨$⟩_ = λ γ → ! ∷ Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ) ∷ 𝓏)))
        ; cong = λ γ →
          ∷-congᵣ (Λ-cong (𝒵-cong {γ = Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ _) ∷ 𝓏)} (∘-congᵣ (∷-congₗ (π-cong (cong (Γf.η Δ) γ))))))
        }
      ; commute = h₁-commute
      })

    h₂ : NaturalTransformation (CommaObj.α Γ) (𝓡₀ A Psh.^ 𝓡₀ B)
    h₂ = Psh.Λ (Psh.counit Psh.∘ Comma⇒.g f)

    coherence : ψ {A} {B} Psh.∘ h₁ Psh.≈ ϕ {A} {B} Psh.∘ h₂
    coherence {Δ} {γ₁} {γ₂} γ₁≈γ₂ {Ξ} {y₁ , θ₁} {y₂ , θ₂} (y₁≈y₂ , θ₁≈θ₂) = begin
        ! ∷ (𝓏 [ ! ∷ (Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Δ ⟨$⟩ γ₁) ∷ 𝓏))) [ W.₁ θ₁ ]) ]) ⦅ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁)) ⦆
      ≈⟨ ∷-congᵣ (app-congₗ (𝒵-cong (S.sym (h₁-commute θ₁ (Setoid.sym (Γα.₀ Δ) γ₁≈γ₂))))) ⟩
        ! ∷ Λ (𝒵 (Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∷ 𝓏))) ⦅ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁)) ⦆
      ≈⟨ ∷-congᵣ Λβ ⟩
        ! ∷ 𝒵 (Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∷ 𝓏)) [ id ∷ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁)) ]
      ≈⟨ ∷-congᵣ (sb-comp {γ = Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∷ 𝓏)}) ⟩
        ! ∷ 𝒵 ((Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∷ 𝓏)) ∘ (id ∷ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁))))
      ≈⟨ 𝒵η ⟩
        (Comma⇒.h f ∘ (π (Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∷ 𝓏)) ∘ (id ∷ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁)))
      ≈⟨ ∘-assoc ⟩
        Comma⇒.h f ∘ ((π (Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∷ 𝓏) ∘ (id ∷ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁))))
      ≈⟨ ∘-congᵣ {γ = Comma⇒.h f} (∷-cong₂ (πβ {a = 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁))}) (v𝓏 {γ = id})) ⟩
        Comma⇒.h f ∘ (((Γf.η Ξ ⟨$⟩ (Γα.₁ θ₁ ⟨$⟩ γ₂)) ∘ id) ∷ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁)))
      ≈⟨ ∘-congᵣ (∷-congₗ (S.trans ∘-identityʳ (cong (Γf.η Ξ) (Γα.F-resp-≈ θ₁≈θ₂ (Setoid.refl (Γα.₀ Δ)))))) ⟩
        Comma⇒.h f ∘ ((Γf.η Ξ ⟨$⟩ (Γα.₁ θ₂ ⟨$⟩ γ₂)) ∷ 𝒵 (𝔦₀.η A Ξ ⟨$⟩ (↓₀.η A Ξ ⟨$⟩ y₁)))
      ≈⟨ Comma⇒.commute f ((Γα.F-resp-≈ (𝕎.Equiv.sym 𝕎.identityʳ) (Setoid.refl (Γα.₀ Δ))) , y₁≈y₂) ⟩
        ! ∷ 𝒵 (𝔦₀.η B Ξ ⟨$⟩ (↓₀.η B Ξ ⟨$⟩ proj₂ (fg.η Ξ ⟨$⟩ (Γα.₁ (θ₂ 𝕎.∘ ϵ) ⟨$⟩ γ₂ , y₂))))
      ≈⟨ 𝒵η ⟩
        𝔦₀.η B Ξ ⟨$⟩ (↓₀.η B Ξ ⟨$⟩ proj₂ (fg.η Ξ ⟨$⟩ (Γα.₁ (θ₂ 𝕎.∘ ϵ) ⟨$⟩ γ₂ , y₂)))
      ∎
      where open Reasoning S.setoid
            module fg = NaturalTransformation (Comma⇒.g f)

  Λ′ : CommaObj.α Γ Psh.⇒ 𝓡₀ (A ⇒ B)
  Λ′ = Pullback.universal (ψ {A} {B} Psh.⊗ ϕ {A} {B}) {h₁ = h₁} {h₂ = h₂} coherence

  module _ {Δ} {x₁} {x₂} where
    private module fg = NaturalTransformation (Comma⇒.g f)

    Λ-commute : Setoid._≈_ (Functor.₀ (CommaObj.α Γ) Δ) x₁ x₂
                → ! ∷ Λ (𝒵 (Comma⇒.h f)) [ Γf.η Δ ⟨$⟩ x₁ ] S.≈
                    ! ∷ Λ (𝒵 (𝔦₀.η B (Δ · A) ⟨$⟩ (↓₀.η B (Δ · A) ⟨$⟩
                    (proj₂ (fg.η (Δ · A) ⟨$⟩
                        (Γα.₁ (ω₁ ϵ) ⟨$⟩ x₂ , ↑₀.η A (Δ · A) ⟨$⟩ R.𝓋 R.𝓏))))))
    Λ-commute x₁≈x₂ = ∷-congᵣ (begin
        Λ (𝒵 (Comma⇒.h f)) [ Γf.η Δ ⟨$⟩ x₁ ]
      ≈⟨ sb-lam ⟩
        Λ (𝒵 (Comma⇒.h f) [ ↑[ Γf.η Δ ⟨$⟩ x₁ ] ])
      ≈⟨ Λ-cong (sb-comp {γ = Comma⇒.h f}) ⟩
        Λ (𝒵 (Comma⇒.h f ∘ ↑[ Γf.η Δ ⟨$⟩ x₁ ]))
      ≈⟨
        Λ-cong (𝒵-cong (∘-congᵣ {γ = Comma⇒.h f} (∷-congₗ (S.sym
          (S.trans
            ∘-identityˡ
            (S.trans
              (∘-congᵣ (S.trans (∘-congₗ (W.identity {A = Δ})) ∘-identityˡ))
              (S.trans π-lemma (π-cong ∘-identityʳ))))))))
      ⟩
        _
      ≈⟨ Λ-cong (𝒵-cong (∘-congᵣ {γ = Comma⇒.h f} (∷-cong₂ (Γf.sym-commute (ω₁ ϵ) (Setoid.refl (Γα.₀ Δ))) (C.sym (𝒵-cong (yoga₀ PE.refl)))))) ⟩
        Λ (𝒵 (Comma⇒.h f ∘ ((Γf.η (Δ · A) ⟨$⟩ (Γα.₁ (ω₁ ϵ) ⟨$⟩ x₁)) ∷ 𝒵 (𝔦₀.η A (Δ · A) ⟨$⟩ (↓₀.η A (Δ · A) ⟨$⟩ (↑₀.η A (Δ · A) ⟨$⟩ R.𝓋 R.𝓏))))))
      ≈⟨ Λ-cong (𝒵-cong (Comma⇒.commute f ((cong (Γα.₁ (ω₁ ϵ)) x₁≈x₂) , cong (↑₀.η A (Δ · A)) PE.refl))) ⟩
        Λ (𝒵 (𝔦₀.η B (Δ · A) ⟨$⟩ (↓₀.η B (Δ · A) ⟨$⟩ (proj₂ (fg.η (Δ · A) ⟨$⟩ (Γα.₁ (ω₁ ϵ) ⟨$⟩ x₂ ,  ↑₀.η A (Δ · A) ⟨$⟩ R.𝓋 R.𝓏))))))
      ∎)
      where open Reasoning C.setoid

  Gl-Λ : Γ Gl.⇒ ⊤ × (A ⇒ B)
  Gl-Λ = record
    { g = Psh.unit Psh.∘ Λ′
    ; h = ! ∷ Λ (𝒵 (Comma⇒.h f))
    ; commute = λ {Δ} {x₁} {x₂} x₁≈x₂ → Λ-commute {Δ} {x₁} {x₂} x₁≈x₂
    }
