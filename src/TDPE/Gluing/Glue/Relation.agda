{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Relation {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma⇒; Cod; Dom)

open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Glue.Yoga 𝒰 hiding (ϕ)
open import TDPE.Gluing.Glue.CartesianClosed 𝒰

import TDPE.Gluing.Interpretation 𝒰 Gl as Interpretation
open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ω₁; ϵ)
import TDPE.Gluing.Representation 𝒰 as R
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh
import TDPE.Gluing.Categories.Category.Instance.Setoids {a} as Setoids

⟦_⟧ = Interpretation.⟦_⟧ CCC
module ⟦_⟧ = Functor ⟦_⟧

gl : Functor Gl 𝕋𝕞
gl = Cod {A = Psh.Psh} Categories.Functor.id Tm

Π : Functor Gl Psh.Psh
Π = Dom {A = Psh.Psh} Categories.Functor.id Tm

⟦-⟧ : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {Γ} {Δ} Setoids.⇒ Category.hom-setoid Gl {⟦_⟧.₀ Γ} {⟦_⟧.₀ Δ}
⟦-⟧ = record
  { _⟨$⟩_ = ⟦_⟧.₁
  ; cong = ⟦_⟧.F-resp-≈
  }

private
  I : ∀ {Δ} → Functor.₀ Π (⟦_⟧.₀ Δ) ≡ 𝓡 Δ
  I {𝟙}     = PE.refl
  I {Δ · A} = PE.cong (Psh._× 𝓡₀ A) (I {Δ})

Π′ : ∀ {Δ Γ} → Category.hom-setoid Gl {⟦_⟧.₀ Γ} {⟦_⟧.₀ Δ} Setoids.⇒ Category.hom-setoid Psh.Psh {𝓡 Γ} {𝓡 Δ}
Π′ {Δ} {Γ} rewrite PE.sym (I {Γ}) rewrite PE.sym (I {Δ}) = record
  { _⟨$⟩_ = Functor.₁ Π
  ; cong = λ {f} {g} f≈g → Functor.F-resp-≈ Π {_} {_} {f} {g} f≈g
  }

identity : ∀ Γ → Setoid.Carrier (𝔑𝔢.₀ Γ Γ)
identity 𝟙       = R.!
identity (Γ · A) = R.ext R.𝔑𝔢₀ (ω₁ ϵ) (identity Γ) R.∷ R.𝓋 R.𝓏

ϕ : ∀ {Δ Γ} → Category.hom-setoid Psh.Psh {𝓡 Γ} {𝓡 Δ} Setoids.⇒ 𝓡.₀ Δ Γ
ϕ {Δ} {Γ} = record
  { _⟨$⟩_ = λ v →  NaturalTransformation.η v Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ identity Γ)
  ; cong = λ v → v (Setoid.refl (𝓡.₀ Γ Γ))
  }

norm : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {Γ} {Δ} Setoids.⇒ 𝔑𝔣.₀ Δ Γ
norm {Δ} {Γ} = ↓.η Δ Γ Setoids.∘ ϕ {Δ} {Γ} Setoids.∘ (Π′ {Δ} {Γ}) Setoids.∘ ⟦-⟧

theorem : ∀ {Δ Γ} {γ : 𝔗𝔪 Γ Δ} → 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ γ) S.≈ γ
theorem {Δ} {Γ} {γ} = begin
    𝔦.η Δ Γ ⟨$⟩ (↓.η Δ Γ ⟨$⟩ ({!!}))
  ≈⟨ {!!} ⟩
    γ
  ∎
  where open Reasoning S.setoid


complete : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Γ Δ}
           → 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ γ) S.≈ 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ δ)
           → γ S.≈ δ
complete {γ = γ} {δ = δ} eq =
  S.trans (S.sym (theorem {γ = γ})) (S.trans eq (theorem {γ = δ}))
