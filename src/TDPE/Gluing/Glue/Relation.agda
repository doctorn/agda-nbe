{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Relation {a} (𝒰 : Set a) where

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)

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

private

  subst-lemma₁ : ∀ {Δ Δ′ Γ A γ a} (p : Δ ≡ Δ′)
                 → PE.subst (𝔗𝔪 Γ) (PE.cong (_· A) p) (γ ∷ a) ≡ PE.subst (𝔗𝔪 Γ) p γ  ∷ a
  subst-lemma₁ PE.refl = PE.refl

  subst-lemma₂ : ∀ {Γ} {F F′ : Psh.Obj} (p : F ≡ F′)
                 → {Δ Δ′ : ℭ} (q : Δ ≡ Δ′)
                 → (η : F Psh.⇒ Tm.₀ Δ) {γ : Setoid.Carrier (Functor.₀ F′ Γ)}
                 → PE.subst (𝔗𝔪 Γ) q (NaturalTransformation.η η Γ ⟨$⟩ PE.subst (λ F → Setoid.Carrier (Functor.₀ F Γ)) (PE.sym p) γ)
                   ≡ NaturalTransformation.η (PE.subst₂ Psh._⇒_ p (PE.cong Tm.₀ q) η) Γ ⟨$⟩ γ
  subst-lemma₂ PE.refl PE.refl η = PE.refl

  subst-S-cong : ∀ {Δ Δ′ Γ} {γ δ : 𝔗𝔪 Γ Δ} (p : Δ ≡ Δ′) → γ S.≈ δ → PE.subst (𝔗𝔪 Γ) p γ S.≈ PE.subst (𝔗𝔪 Γ) p δ
  subst-S-cong PE.refl x = x

  subst-× : ∀ {F F′ : Psh.Obj} {A Γ γ a} (p : F ≡ F′)
            → PE.subst (λ F → Setoid.Carrier (Functor.₀ F Γ)) (PE.sym (PE.cong (Psh._× 𝓡₀ A) p)) (γ , a)
              ≡ (PE.subst (λ F → Setoid.Carrier (Functor.₀ F Γ)) (PE.sym  p) γ , a)
  subst-× PE.refl = PE.refl

  subst-∘-NT : ∀ {F F′ G G′ H H′ : Psh.Obj} {η : F Psh.⇒ G} {ϵ : G Psh.⇒ H}
               → (p : F ≡ F′) (q : G ≡ G′) (r : H ≡ H′)
               → PE.subst₂ Psh._⇒_ q r ϵ Psh.∘ PE.subst₂ Psh._⇒_ p q η
                   ≡ PE.subst₂ Psh._⇒_ p r (ϵ Psh.∘ η)
  subst-∘-NT PE.refl PE.refl PE.refl = PE.refl

  subst-η-NT : ∀ {F F′ G G′ : Psh.Obj} {η : F Psh.⇒ G} {Ξ}
               → (p : F ≡ F′) (q : G ≡ G′)
               → NaturalTransformation.η (PE.subst₂ Psh._⇒_ p q η) Ξ
                   ≡ PE.subst₂ Setoids._⇒_ (PE.cong₂ Functor.₀ p PE.refl) (PE.cong₂ Functor.₀ q PE.refl) (NaturalTransformation.η η Ξ)
  subst-η-NT PE.refl PE.refl = PE.refl

  -- FIXME(@doctorn) this should generalise to arbitrary functors
  subst-F : ∀ {Δ Δ′ Γ Γ′} (p : Δ ≡ Δ′) (q : Γ ≡ Γ′) (γ : 𝔗𝔪 Δ Γ)
            → Tm.₁ (PE.subst₂ 𝔗𝔪 p q γ) ≡ PE.subst₂ Psh._⇒_ (PE.cong Tm.₀ p) (PE.cong Tm.₀ q) (Tm.₁ γ)
  subst-F PE.refl PE.refl γ = PE.refl

⟦_⟧ = Interpretation.⟦_⟧ CCC
module ⟦_⟧ = Functor ⟦_⟧

gl : Functor Gl 𝕋𝕞
gl = Cod {A = Psh.Psh} Categories.Functor.id Tm
module gl = Functor gl

prj : Functor Gl Psh.Psh
prj = Dom {A = Psh.Psh} Categories.Functor.id Tm
module prj = Functor prj

private
  gl-lemma : ∀ {Δ} → gl.₀ (⟦_⟧.₀ Δ) ≡ Δ
  gl-lemma {𝟙}     = PE.refl
  gl-lemma {Δ · A} = PE.cong (_· A) gl-lemma

  prj-lemma : ∀ {Δ} → prj.₀ (⟦_⟧.₀ Δ) ≡ 𝓡 Δ
  prj-lemma {𝟙}     = PE.refl
  prj-lemma {Δ · A} = PE.cong (Psh._× 𝓡₀ A) (prj-lemma {Δ})

  q₀ : (Δ : ℭ) → prj.₀ (⟦_⟧.₀ Δ) Psh.⇒ Tm.₀ (gl.₀ (⟦_⟧.₀ Δ))
  q₀ Δ = CommaObj.f (⟦_⟧.₀ Δ)

  q : (Δ : ℭ) → 𝓡 Δ Psh.⇒ Tm.₀ Δ
  q Δ = PE.subst₂ Psh._⇒_ (prj-lemma {Δ}) (PE.cong Tm.₀ (gl-lemma {Δ})) (q₀ Δ)

  q-lemma : ∀ {Δ} → q Δ Psh.≈ 𝔦 Δ Psh.∘ ↓ Δ
  q-lemma {𝟙}     {Γ} {tt}    {tt}    tt          = !η
  q-lemma {Δ · A} {Γ} {γ , a} {δ , b} (γ≈δ , a≈b) = begin
      NaturalTransformation.η (q (Δ · A)) Γ ⟨$⟩ (γ , a)
    ≈⟨ S.sym (Setoid.reflexive S.setoid (subst-lemma₂ (prj-lemma {Δ · A}) (PE.cong (_· A) (gl-lemma {Δ})) (q₀ (Δ · A)))) ⟩
      PE.subst (𝔗𝔪 Γ) (PE.cong (_· A) (gl-lemma {Δ}))
        (NaturalTransformation.η (q₀ (Δ · A)) Γ ⟨$⟩ (PE.subst (λ F → Setoid.Carrier (Functor.₀ F Γ)) (PE.sym (prj-lemma {Δ · A})) (γ , a)))
    ≡⟨ PE.cong (PE.subst (𝔗𝔪 Γ) (PE.cong (_· A) (gl-lemma {Δ}))) (PE.cong (NaturalTransformation.η (q₀ (Δ · A)) Γ ⟨$⟩_) (subst-× {A = A} (prj-lemma {Δ}))) ⟩
      PE.subst (𝔗𝔪 Γ) (PE.cong (_· A) (gl-lemma {Δ}))
        ((NaturalTransformation.η (q₀ Δ) Γ ⟨$⟩
          (PE.subst (λ F → Setoid.Carrier (Functor.₀ F Γ)) (PE.sym (prj-lemma {Δ})) γ)) ∷ 𝒵 (𝔦₀.η A Γ ⟨$⟩ (↓₀.η A Γ ⟨$⟩ a)))
    ≡⟨ subst-lemma₁ (gl-lemma {Δ}) ⟩
      PE.subst (𝔗𝔪 Γ) (gl-lemma {Δ})
        (NaturalTransformation.η (q₀ Δ) Γ ⟨$⟩
          (PE.subst (λ F → Setoid.Carrier (Functor.₀ F Γ)) (PE.sym (prj-lemma {Δ})) γ)) ∷ 𝒵 (𝔦₀.η A Γ ⟨$⟩ (↓₀.η A Γ ⟨$⟩ a))
    ≈⟨ ∷-congₗ (Setoid.reflexive S.setoid (subst-lemma₂ (prj-lemma {Δ}) (gl-lemma {Δ}) (q₀ Δ))) ⟩
      (NaturalTransformation.η (q Δ) Γ ⟨$⟩ γ) ∷ 𝒵 (𝔦₀.η A Γ ⟨$⟩ (↓₀.η A Γ ⟨$⟩ a))
    ≈⟨ ∷-cong₂ (q-lemma γ≈δ) (𝒵-cong (cong (𝔦₀.η A Γ Setoids.∘ ↓₀.η A Γ) a≈b)) ⟩
      (𝔦.η Δ Γ ⟨$⟩ (↓.η Δ Γ ⟨$⟩ δ)) ∷ 𝒵 (𝔦₀.η A Γ ⟨$⟩ (↓₀.η A Γ ⟨$⟩ b))
    ∎
    where open Reasoning S.setoid

  gl₁ : ∀ {Δ Γ} → ⟦_⟧.₀ Δ Gl.⇒ ⟦_⟧.₀ Γ → 𝔗𝔪 Δ Γ
  gl₁ {Δ} {Γ} γ = PE.subst₂ (Category._⇒_ 𝕋𝕞) (gl-lemma {Δ}) (gl-lemma {Γ}) (gl.₁ γ)

  gl₁-cong : ∀ {Δ Γ} {γ δ : ⟦_⟧.₀ Δ Gl.⇒ ⟦_⟧.₀ Γ} → γ Gl.≈ δ → gl₁ {Δ} {Γ} γ S.≈ gl₁ {Δ} {Γ} δ
  gl₁-cong {Δ} {Γ} {γ} {δ} γ≈δ = 𝓕* (gl-lemma {Δ}) (gl-lemma {Γ}) (gl.F-resp-≈ {⟦_⟧.₀ Δ} {⟦_⟧.₀ Γ} {γ} {δ} γ≈δ)
    where 𝓕* : ∀ {Δ Δ′ Γ Γ′ : ℭ} (p : Δ ≡ Δ′) (q : Γ ≡ Γ′) {γ δ : 𝔗𝔪 Δ Γ} → γ S.≈ δ → PE.subst₂ 𝔗𝔪 p q γ S.≈ PE.subst₂ 𝔗𝔪 p q δ
          𝓕* PE.refl PE.refl γ≈δ = γ≈δ

  gl′ : ∀ {Δ Γ} → Category.hom-setoid Gl {⟦_⟧.₀ Δ} {⟦_⟧.₀ Γ} Setoids.⇒ Category.hom-setoid 𝕋𝕞 {Δ} {Γ}
  gl′ {Δ} {Γ} = record
    { _⟨$⟩_ = gl₁
    ; cong = λ {γ} {δ} γ≈δ → gl₁-cong {Δ} {Γ} {γ} {δ} γ≈δ
    }

  prj₁ : ∀ {Δ Γ} → ⟦_⟧.₀ Δ Gl.⇒ ⟦_⟧.₀ Γ → (𝓡 Δ) Psh.⇒ (𝓡 Γ)
  prj₁ {Δ} {Γ} γ = PE.subst₂ Psh._⇒_ (prj-lemma {Δ}) (prj-lemma {Γ}) (prj.₁ γ)

  prj₁-cong : ∀ {Δ Γ} {γ δ : ⟦_⟧.₀ Δ Gl.⇒ ⟦_⟧.₀ Γ} → γ Gl.≈ δ → prj₁ {Δ} {Γ} γ Psh.≈ prj₁ {Δ} {Γ} δ
  prj₁-cong {Δ} {Γ} {γ} {δ} γ≈δ = 𝓕* (prj-lemma {Δ}) (prj-lemma {Γ}) (prj.F-resp-≈ {⟦_⟧.₀ Δ} {⟦_⟧.₀ Γ} {γ} {δ} γ≈δ)
    where 𝓕* : ∀ {Δ Δ′ Γ Γ′ : Psh.Obj} (p : Δ ≡ Δ′) (q : Γ ≡ Γ′) {γ δ : Δ Psh.⇒ Γ} → γ Psh.≈ δ → PE.subst₂ Psh._⇒_ p q γ Psh.≈ PE.subst₂ Psh._⇒_ p q δ
          𝓕* PE.refl PE.refl γ≈δ = γ≈δ

  prj′ : ∀ {Δ Γ} → Category.hom-setoid Gl {⟦_⟧.₀ Δ} {⟦_⟧.₀ Γ} Setoids.⇒ Category.hom-setoid Psh.Psh {𝓡 Δ} {𝓡 Γ}
  prj′ {Δ} {Γ} = record
    { _⟨$⟩_ = λ γ → PE.subst₂ Psh._⇒_ (prj-lemma {Δ}) (prj-lemma {Γ}) (prj.₁ γ)
    ; cong = λ {γ} {δ} γ≈δ → prj₁-cong {Δ} {Γ} {γ} {δ} γ≈δ
    }

  ⟦_⟧′ : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {Δ} {Γ} Setoids.⇒ Category.hom-setoid Gl {⟦_⟧.₀ Δ} {⟦_⟧.₀ Γ}
  ⟦_⟧′ = record
    { _⟨$⟩_ = ⟦_⟧.₁
    ; cong = ⟦_⟧.F-resp-≈
    }

ϕ : ∀ {Δ Γ} → Category.hom-setoid Psh.Psh {𝓡 Γ} {𝓡 Δ} Setoids.⇒ 𝓡.₀ Δ Γ
ϕ {Δ} {Γ} = record
  { _⟨$⟩_ = λ v →  NaturalTransformation.η v Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ)
  ; cong = λ v → v (Setoid.refl (𝓡.₀ Γ Γ))
  }

norm : ∀ {Δ Γ} → Category.hom-setoid 𝕋𝕞 {Γ} {Δ} Setoids.⇒ 𝔑𝔣.₀ Δ Γ
norm {Δ} {Γ} = ↓.η Δ Γ Setoids.∘ ϕ {Δ} {Γ} Setoids.∘ prj′ {Γ} {Δ} Setoids.∘ ⟦_⟧′

theorem : ∀ {Δ Γ} {γ : 𝔗𝔪 Γ Δ} → 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ γ) S.≈ γ
theorem {Δ} {Γ} {γ} = begin
    𝔦.η Δ Γ ⟨$⟩ (↓.η Δ Γ ⟨$⟩ (v.η Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ)))
  ≈⟨ S.sym (q-lemma (Setoid.refl (Functor.₀ (𝓡 Δ) Γ))) ⟩
    NaturalTransformation.η (q Δ) Γ ⟨$⟩ (v.η Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ))
  ≈⟨ S.sym (commute (Setoid.refl (Functor.₀ (𝓡 Γ) Γ))) ⟩
    δ ∘ (NaturalTransformation.η (q Γ) Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ))
  ≈⟨ ∘-congᵣ (q-lemma (Setoid.refl (Functor.₀ (𝓡 Γ) Γ))) ⟩
    δ ∘ (𝔦.η Γ Γ ⟨$⟩ (↓.η Γ Γ ⟨$⟩ (↑.η Γ Γ ⟨$⟩ R.identity Γ)))
  ≈⟨ ∘-congᵣ (yoga (Setoid.refl (𝔑𝔢.₀ Γ Γ))) ⟩
    δ ∘ (𝔦′.η Γ Γ ⟨$⟩ R.identity Γ)
  ≈⟨ ∘-congᵣ (𝔦′-id Γ) ⟩
    δ ∘ id
  ≈⟨ ∘-identityʳ ⟩
    δ
  ≡⟨⟩
    gl′ ⟨$⟩ (⟦_⟧.₁ γ)
  ≈⟨ {!!} ⟩
    γ
  ∎
  where v = prj′ {Γ} {Δ} ⟨$⟩ (⟦_⟧.₁ γ)
        δ = gl′ ⟨$⟩ (⟦_⟧.₁ γ)

        module v = NaturalTransformation v

        v₀ = prj.₁ (⟦_⟧.₁ γ)
        δ₀ = gl.₁ (⟦_⟧.₁ γ)

        module v₀ = NaturalTransformation v₀

        commute₀ : Tm.₁ δ₀ Psh.∘ q₀ Γ Psh.≈ q₀ Δ Psh.∘ v₀
        commute₀ = Comma⇒.commute (⟦_⟧.₁ γ)

        commute :  Tm.₁ δ Psh.∘ q Γ Psh.≈ q Δ Psh.∘ v
        commute {Ξ} {x} {y} x≈y = begin
            NaturalTransformation.η
              (Tm.₁ (PE.subst₂ 𝔗𝔪 (gl-lemma {Γ}) (gl-lemma {Δ}) δ₀)
                Psh.∘ (PE.subst₂ Psh._⇒_ (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Γ})) (q₀ Γ))) Ξ ⟨$⟩ x
          ≡⟨ PE.cong (λ δ → NaturalTransformation.η (δ Psh.∘ PE.subst₂ Psh._⇒_ (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Γ})) (q₀ Γ)) Ξ ⟨$⟩ x) (subst-F (gl-lemma {Γ}) (gl-lemma {Δ}) δ₀) ⟩
            NaturalTransformation.η
              (PE.subst₂ Psh._⇒_ (PE.cong Tm.₀ (gl-lemma {Γ})) (PE.cong Tm.₀ (gl-lemma {Δ})) (Tm.₁ δ₀)
                Psh.∘ (PE.subst₂ Psh._⇒_ (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Γ})) (q₀ Γ))) Ξ ⟨$⟩ x
          ≡⟨ PE.cong (λ η → NaturalTransformation.η η Ξ ⟨$⟩ x) (subst-∘-NT (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Γ})) (PE.cong Tm.₀ (gl-lemma {Δ}))) ⟩
            NaturalTransformation.η (PE.subst₂ Psh._⇒_ (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Δ})) (Tm.₁ δ₀ Psh.∘ q₀ Γ)) Ξ ⟨$⟩ x
          ≡⟨ PE.cong (_⟨$⟩ x) (subst-η-NT (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Δ}))) ⟩
            PE.subst₂ Setoids._⇒_
              (PE.cong₂ Functor.₀ (prj-lemma {Γ}) PE.refl)
              (PE.cong₂ Functor.₀ (PE.cong Tm.₀ (gl-lemma {Δ})) PE.refl)
              (NaturalTransformation.η (Tm.₁ δ₀ Psh.∘ q₀ Γ) Ξ) ⟨$⟩ x
          ≈⟨ {!!} ⟩
            PE.subst₂ Setoids._⇒_
              (PE.cong₂ Functor.₀ (prj-lemma {Γ}) PE.refl)
              (PE.cong₂ Functor.₀ (PE.cong Tm.₀ (gl-lemma {Δ})) PE.refl)
              (NaturalTransformation.η (q₀ Δ Psh.∘ v₀) Ξ) ⟨$⟩ y
          ≡⟨ PE.sym (PE.cong (_⟨$⟩ y) (subst-η-NT (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Δ})))) ⟩
            NaturalTransformation.η (PE.subst₂ Psh._⇒_ (prj-lemma {Γ}) (PE.cong Tm.₀ (gl-lemma {Δ})) (q₀ Δ Psh.∘ v₀)) Ξ ⟨$⟩ y
          ≡⟨ PE.sym (PE.cong (λ η → NaturalTransformation.η η Ξ ⟨$⟩ y) (subst-∘-NT (prj-lemma {Γ}) (prj-lemma {Δ}) (PE.cong Tm.₀ (gl-lemma {Δ}))))  ⟩
            NaturalTransformation.η
              (PE.subst₂ Psh._⇒_ (prj-lemma {Δ}) (PE.cong Tm.₀ (gl-lemma {Δ})) (q₀ Δ)
                Psh.∘ PE.subst₂ Psh._⇒_ (prj-lemma {Γ}) (prj-lemma {Δ}) v₀) Ξ ⟨$⟩ y
          ∎
          where open Reasoning S.setoid

        open Reasoning S.setoid

complete : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Γ Δ}
           → 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ γ) S.≈ 𝔦.η Δ Γ ⟨$⟩ (norm ⟨$⟩ δ)
           → γ S.≈ δ
complete {γ = γ} {δ = δ} eq =
  S.trans (S.sym (theorem {γ = γ})) (S.trans eq (theorem {γ = δ}))
