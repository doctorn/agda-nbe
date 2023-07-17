{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Relation {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Category.Construction.Comma using (CommaObj; Comma⇒; Cod; Dom)

open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Glue.Yoga 𝒰 hiding (ϕ)
open import TDPE.Gluing.Glue.CartesianClosed 𝒰

import TDPE.Gluing.Interpretation 𝒰 Gl as Interpretation
open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Embedding 𝒰
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ω₁; ϵ)
import TDPE.Gluing.Representation 𝒰 as R
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh
import TDPE.Gluing.Categories.Category.Instance.Setoids {a} as Setoids

⟦_⟧ = Interpretation.⟦_⟧ CCC
module ⟦_⟧ = Functor ⟦_⟧

gl : Functor Gl 𝕋𝕞
gl = Cod {A = Psh.Psh} Categories.Functor.id Tm
module gl = Functor gl

prj : Functor Gl Psh.Psh
prj = Dom {A = Psh.Psh} Categories.Functor.id Tm
module prj = Functor prj

private
  I : ∀ {Δ} → gl.₀ (⟦_⟧.₀ Δ) ≡ Δ
  I {𝟙}     = PE.refl
  I {Δ · A} = PE.cong (_· A) I

  II : ∀ {Δ} → prj.₀ (⟦_⟧.₀ Δ) ≡ 𝓡 Δ
  II {𝟙}     = PE.refl
  II {Δ · A} = PE.cong (Psh._× 𝓡₀ A) (II {Δ})

  adjust : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {gl.₀ (⟦_⟧.₀ Γ)} {gl.₀ (⟦_⟧.₀ Δ)} Setoids.⇒ Category.hom-setoid 𝕋𝕞 {Γ} {Δ}
  adjust = record { _⟨$⟩_ = |adjust| ; cong = adjust-cong }
    where  |adjust| : ∀ {Δ Γ} → 𝔗𝔪 (gl.₀ (⟦_⟧.₀ Γ)) (gl.₀ (⟦_⟧.₀ Δ)) → 𝔗𝔪 Γ Δ
           |adjust| {Δ} {Γ} f rewrite I {Δ} | I {Γ} = f

           adjust-cong : ∀ {Δ Γ} {γ δ : 𝔗𝔪 (gl.₀ (⟦_⟧.₀ Γ)) (gl.₀ (⟦_⟧.₀ Δ))} → γ S.≈ δ → |adjust| {Δ} {Γ} γ S.≈ |adjust| {Δ} {Γ} δ
           adjust-cong {Δ} {Γ} γ≈δ rewrite I {Δ} | I {Γ} = γ≈δ

⟦_⟧₁ : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {Γ} {Δ} Setoids.⇒ Category.hom-setoid Gl {⟦_⟧.₀ Γ} {⟦_⟧.₀ Δ}
⟦_⟧₁ = record
  { _⟨$⟩_ = ⟦_⟧.₁
  ; cong = ⟦_⟧.F-resp-≈
  }

gl₁ : ∀ {Δ Γ} → Category.hom-setoid Gl {⟦_⟧.₀ Γ} {⟦_⟧.₀ Δ} Setoids.⇒ Category.hom-setoid 𝕋𝕞 {Γ} {Δ}
gl₁ {Δ} {Γ} = record
  { _⟨$⟩_ = λ f → adjust {Δ} {Γ} ⟨$⟩ gl.₁ f
  ; cong = λ {f} {g} f≈g → cong adjust (gl.F-resp-≈ {⟦_⟧.₀ Γ} {⟦_⟧.₀ Δ} {f} {g} f≈g)
  }

prj₁ : ∀ {Δ Γ} → Category.hom-setoid Gl {⟦_⟧.₀ Γ} {⟦_⟧.₀ Δ} Setoids.⇒ Category.hom-setoid Psh.Psh {𝓡 Γ} {𝓡 Δ}
prj₁ {Δ} {Γ} rewrite PE.sym (II {Γ}) | PE.sym (II {Δ}) = record
  { _⟨$⟩_ = prj.₁
  ; cong = λ {f} {g} f≈g → prj.F-resp-≈ {_} {_} {f} {g} f≈g
  }

commutes : ∀ {Δ Γ} (γ : 𝔗𝔪 Γ Δ)
           → 𝔦 Δ Psh.∘ ↓ Δ Psh.∘ (prj₁ {Δ} {Γ} ⟨$⟩ ⟦_⟧.₁ γ) Psh.≈ Tm.₁ (gl₁ ⟨$⟩ ⟦_⟧.₁ γ) Psh.∘ 𝔦 Γ Psh.∘ ↓ Γ
commutes {Δ} {Γ} γ {Ξ} {x} {y} x≈y = begin
    𝔦.η Δ Ξ ⟨$⟩ (↓.η Δ Ξ ⟨$⟩ (NaturalTransformation.η (prj₁ {Δ} {Γ} ⟨$⟩ ⟦_⟧.₁ γ) Ξ ⟨$⟩ x))
  ≈⟨ {!!} ⟩
    (gl₁ ⟨$⟩ ⟦_⟧.₁ γ) ∘ (𝔦.η Γ Ξ ⟨$⟩ (↓.η Γ Ξ ⟨$⟩ y))
  ∎
  where open Reasoning S.setoid

ϕ : ∀ {Δ Γ} → Category.hom-setoid Psh.Psh {𝓡 Γ} {𝓡 Δ} Setoids.⇒ 𝓡.₀ Δ Γ
ϕ {Δ} {Γ} = record
  { _⟨$⟩_ = λ v →  NaturalTransformation.η v Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ)
  ; cong = λ v → v (Setoid.refl (𝓡.₀ Γ Γ))
  }

norm : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {Γ} {Δ} Setoids.⇒ 𝔑𝔣.₀ Δ Γ
norm {Δ} {Γ} = ↓.η Δ Γ Setoids.∘ ϕ {Δ} {Γ} Setoids.∘ (prj₁ {Δ} {Γ}) Setoids.∘ ⟦_⟧₁

theorem : ∀ {Δ Γ} {γ : 𝔗𝔪 Γ Δ} → 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ γ) S.≈ γ
theorem {Δ} {Γ} {γ} = begin
    𝔦.η Δ Γ ⟨$⟩ (↓.η Δ Γ ⟨$⟩ (v.η Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ)))
  ≈⟨ commutes {Δ} {Γ} γ (Setoid.refl (𝓡.₀ Γ Γ)) ⟩
    δ ∘ (𝔦.η Γ Γ ⟨$⟩ (↓.η Γ Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ)))
  ≈⟨ ∘-congᵣ (yoga (Setoid.refl (𝔑𝔢.₀ Γ Γ))) ⟩
    δ ∘ (𝔦′.η Γ Γ ⟨$⟩ R.identity Γ)
  ≈⟨ ∘-congᵣ (𝔦′-id Γ) ⟩
    δ ∘ id
  ≈⟨ ∘-identityʳ ⟩
    δ
  ≡⟨⟩
    gl₁ {Δ} {Γ} ⟨$⟩ ⟦_⟧.₁ γ
  ≈⟨ {!!} ⟩
    γ
  ∎
  where open Reasoning S.setoid

        v = prj₁ {Δ} {Γ} ⟨$⟩ ⟦_⟧.₁ γ
        δ = gl₁ {Δ} {Γ} ⟨$⟩ ⟦_⟧.₁ γ

        module v = NaturalTransformation v

complete : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Γ Δ}
           → 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ γ) S.≈ 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ δ)
           → γ S.≈ δ
complete {γ = γ} {δ = δ} eq =
  S.trans (S.sym (theorem {γ = γ})) (S.trans eq (theorem {γ = δ}))
