{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Base {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma)
open import Categories.Yoneda

open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import TDPE.Gluing.Categories.Functor.Properties using (precompose)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ⟦_⟧; ω₁; ω₂; 𝒲)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Representation 𝒰 as Repr
  using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣; 𝓋; 𝓏; π; ι; Λ; _⦅_⦆)
import TDPE.Gluing.Syntax 𝒰 as S
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

W = ⟦_⟧ S.CC

module W = Functor W

Tm : Functor S.𝕋𝕞 Psh.Psh
Tm = precompose (Functor.op W) ∘F Yoneda.embed S.𝕋𝕞

module Tm = Functor Tm

module _ A where module 𝔑𝔣₀ = Functor (𝔑𝔣₀ A)
module _ A where module 𝔑𝔢₀ = Functor (𝔑𝔢₀ A)
module _ Γ where module 𝔑𝔣 = Functor (𝔑𝔣 Γ)
module _ Γ where module 𝔑𝔢 = Functor (𝔑𝔢 Γ)

private

  𝔦₀-η : ∀ A Γ → Setoid.Carrier (𝔑𝔣₀.₀ A Γ) → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)
  𝔦₀′-η : ∀ A Γ → Setoid.Carrier (𝔑𝔢₀.₀ A Γ) → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)

  𝔦₀-cong : ∀ A Γ {x y : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)} → x ≡ y → 𝔦₀-η A Γ x S.S.≈ 𝔦₀-η A Γ y
  𝔦₀′-cong : ∀ A Γ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)} → x ≡ y → 𝔦₀′-η A Γ x S.S.≈ 𝔦₀′-η A Γ y

  𝔦₀-commute : ∀ A {Γ Δ} (f : 𝒲 Δ Γ) {x y : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)}
               → x ≡ y → 𝔦₀-η A Δ (Repr.+ f x) S.S.≈ S.! S.∷ S.𝓏 S.[ 𝔦₀-η A Γ y S.∘ W.₁ f ]
  𝔦₀′-commute : ∀ A {Γ Δ} (f : 𝒲 Δ Γ) {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
               → x ≡ y → 𝔦₀′-η A Δ (Repr.+′ f x) S.S.≈ S.! S.∷ S.𝓏 S.[ 𝔦₀′-η A Γ y S.∘ W.₁ f ]

  v : ∀ {Γ A} → Repr.var Γ A → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)
  v 𝓏     = S.! S.∷ S.𝓏
  v (π x) = S.! S.∷ S.p (S.𝒵 (v x))

  𝔦₀-η _       Γ (ι x) = 𝔦₀′-η _ Γ x
  𝔦₀-η (A ⇒ B) Γ (Λ x) = S.! S.∷ S.Λ (S.𝒵 (𝔦₀-η B (Γ · A) x))

  𝔦₀′-η A Γ (𝓋 x)     = v x
  𝔦₀′-η A Γ (f ⦅ x ⦆) = S.! S.∷ S.𝒵 (𝔦₀′-η _ Γ f) S.⦅ S.𝒵 (𝔦₀-η _ Γ x) ⦆

  -- NOTE(@doctorn) these proofs could just be done with `Setoid.reflexive`, but I wanted to future proof
  -- them a bit for partial evaluation
  𝔦₀-cong _       Γ {ι x} PE.refl = 𝔦₀′-cong _ Γ {x} PE.refl
  𝔦₀-cong (A ⇒ B) Γ {Λ x} PE.refl = S.∷-congᵣ (S.Λ-cong (S.𝒵-cong (𝔦₀-cong B (Γ · A) {x} PE.refl)))

  𝔦₀′-cong A Γ {𝓋 x}    PE.refl = Setoid.reflexive (Functor.₀ (Tm.₀ (𝟙 · A)) Γ) PE.refl
  𝔦₀′-cong A Γ {f ⦅ x ⦆} PE.refl =
    S.∷-congᵣ (S.app-cong₂ (S.𝒵-cong (𝔦₀′-cong _ Γ {f} PE.refl))
      (S.𝒵-cong (𝔦₀-cong _ Γ {x} PE.refl)))

  𝔦₀-commute _       f {x = ι x} PE.refl = 𝔦₀′-commute _ f {x} PE.refl
  𝔦₀-commute (A ⇒ B) f {x = Λ x} PE.refl = S.∷-congᵣ (begin
      S.Λ (S.𝒵 (𝔦₀-η B _ (Repr.+ (ω₂ f) x)))
    ≈⟨ S.Λ-cong (S.𝒵-cong (𝔦₀-commute B (ω₂ f) {x} PE.refl)) ⟩
      S.Λ (S.𝓏 S.[ 𝔦₀-η B _ x S.∘ _ ])
    ≈⟨ S.Λ-cong S.v𝒵 ⟩
      S.Λ (S.𝒵 (𝔦₀-η B _ x S.∘ _))
    ≈⟨ S.Λ-cong (S.C.sym (S.sb-comp {γ = 𝔦₀-η B _ x})) ⟩
      S.Λ (S.𝒵 (𝔦₀-η _ _ x) S.[ _ ])
    ≈⟨ S.Λ-cong (S.sb-congᵣ (S.∷-congₗ (S.S.trans (S.S.sym S.πβ) S.∘-identityʳ))) ⟩
      S.Λ (S.𝒵 (𝔦₀-η _ _ x) S.[ _ ])
    ≈⟨ S.C.sym S.sb-lam ⟩
      S.Λ (S.𝒵 (𝔦₀-η _ _ x)) S.[ _ ]
    ≈⟨ S.C.sym S.v𝓏 ⟩
      S.𝓏 S.[ (S.! S.∷ S.Λ (S.𝒵 (𝔦₀-η _ _ x))) S.∘ _ ]
    ∎)
    where open Reasoning S.C.setoid

  𝔦₀′-commute A f {𝓋 x} PE.refl =
    S.S.trans (S.S.trans (I f x) (S.S.sym S.𝒵η)) (S.∷-congᵣ (S.C.sym S.v𝒵))
    where I : ∀ {Γ Δ} (f : 𝒲 Δ Γ) (x : Repr.var Γ A)
              → v (Repr.+var f x) S.S.≈ v x S.∘ W.₁ f
          I {Γ · A} {Δ} (ω₁ f) 𝓏 = S.∷-congᵣ (begin
              S.p (S.𝒵 (v (Repr.+var f 𝓏)))
            ≈⟨ S.p-cong (S.𝒵-cong (I f 𝓏)) ⟩
              S.p (S.𝒵 (v (𝓏 {Γ = Γ}) S.∘ W.₁ f))
            ≈⟨ S.p-π ⟩
              S.𝓏 S.[ S.π (W.₁ f) ]
            ≈⟨ S.sb-congᵣ (S.S.sym S.π-id) ⟩
              S.𝓏 S.[ W.₁ f S.∘ S.π S.id ]
            ∎)
            where open Reasoning S.C.setoid
          I {Γ · A} {Δ · A} (ω₂ f) 𝓏 = S.S.sym (S.∷-congᵣ S.v𝓏)
          I {Γ · A} {Δ} (ω₁ f) (π x) = S.∷-congᵣ (begin
              S.p (S.𝒵 (v (Repr.+var f (π x))))
            ≈⟨ S.p-cong (S.𝒵-cong (I f (π x))) ⟩
              S.p (S.p (S.𝒵 (v x)) S.[ W.₁ f ])
            ≈⟨ S.p-π ⟩
              S.p (S.𝒵 (v x)) S.[ S.π (W.₁ f) ]
            ≈⟨ S.sb-congᵣ (S.S.sym S.π-id) ⟩
              S.p (S.𝒵 (v x)) S.[ W.₁ f S.∘ S.π S.id ]
            ∎)
            where open Reasoning S.C.setoid
          I {Γ · A} {Δ · A} (ω₂ f) (π x) = S.∷-congᵣ (begin
              S.p (S.𝒵 (v (Repr.+var f x)))
            ≈⟨ S.p-cong (S.𝒵-cong (I f x)) ⟩
              S.p (S.𝒵 (v x S.∘ W.₁ f))
            ≈⟨ S.𝒵p {γ = v x S.∘ W.₁ f} ⟩
              S.𝓏 S.[ S.π (v x S.∘ W.₁ f) ]
            ≈⟨ S.sb-congᵣ (S.S.sym S.π-lemma) ⟩
              S.𝓏 S.[ v x S.∘ S.π (W.₁ f) ]
            ≈⟨ S.C.sym S.sb-assoc ⟩
              S.𝓏 S.[ v x ] S.[ S.π (W.₁ f) ]
            ≈⟨ S.sb-cong₂ S.v𝒵 (S.S.sym S.π-id) ⟩
              S.𝒵 (v x) S.[ W.₁ f S.∘ S.π S.id ]
            ≈⟨ S.C.sym S.vp ⟩
              S.p (S.𝒵 (v x)) S.[ W.₁ f S.∘ S.π S.id S.∷ S.𝓏 ]
            ∎)
            where open Reasoning S.C.setoid
  𝔦₀′-commute A f {t ⦅ x ⦆} PE.refl = S.∷-congᵣ (begin
      S.𝒵 (𝔦₀′-η _ _ (Repr.+′ f t)) S.⦅ S.𝒵 (𝔦₀-η _ _ (Repr.+ f x)) ⦆
    ≈⟨ S.app-cong₂ (S.𝒵-cong (𝔦₀′-commute _ f {t} PE.refl)) (S.𝒵-cong (𝔦₀-commute _ f {x} PE.refl)) ⟩
      S.𝓏 S.[ _ ] S.⦅ S.𝓏 S.[ _ ] ⦆
    ≈⟨ S.app-cong₂ S.v𝒵 S.v𝒵 ⟩
      _ S.⦅ _ ⦆
    ≈⟨ S.C.sym (S.app-cong₂ (S.sb-comp {γ = 𝔦₀′-η _ _ t}) (S.sb-comp {γ = 𝔦₀-η _ _ x})) ⟩
      _ S.⦅ _ ⦆
    ≈⟨ S.C.sym S.sb-app ⟩
      (S.𝒵 (𝔦₀′-η _ _ t) S.⦅ S.𝒵 (𝔦₀-η _ _ x) ⦆) S.[ _ ]
    ≈⟨ S.C.sym S.v𝓏 ⟩
      S.𝓏 S.[ (S.! S.∷ S.𝒵 (𝔦₀′-η _ _ t) S.⦅ S.𝒵 (𝔦₀-η _ _ x) ⦆) S.∘ _ ]
    ∎)
    where open Reasoning S.C.setoid

𝔦₀ : ∀ A → 𝔑𝔣₀ A Psh.⇒ Tm.₀ (𝟙 · A)
𝔦₀ A = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = 𝔦₀-η A Γ ; cong = 𝔦₀-cong A Γ }
  ; commute = 𝔦₀-commute A
  })

𝔦₀′ : ∀ A → 𝔑𝔢₀ A Psh.⇒ Tm.₀ (𝟙 · A)
𝔦₀′ A = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = 𝔦₀′-η A Γ ; cong = 𝔦₀′-cong A Γ }
  ; commute = 𝔦₀′-commute A
  })

-- TODO(@doctorn) both of these should be constructed via the universal property of extension to substitutions
𝔦 : ∀ Δ → 𝔑𝔣 Δ Psh.⇒ Tm.₀ Δ
𝔦 𝟙       = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = λ _ → S.! ; cong = λ _ → S.!η }
  ; commute = λ _ _ → S.!η
  })
𝔦 (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ Repr.∷ a) → (𝔦Δ.η Γ ⟨$⟩ γ) S.∷ S.𝒵 (𝔦₀A.η Γ ⟨$⟩ a) }
    ; cong = λ { (γ Repr.∷ a) → S.∷-cong₂ (cong (𝔦Δ.η Γ) γ) (S.𝒵-cong (cong (𝔦₀A.η Γ) a)) }
    }
  ; commute = λ f → λ { (γ Repr.∷ a) → commute f γ a }
  })
  where module 𝔦Δ = NaturalTransformation (𝔦 Δ)
        module 𝔦₀A = NaturalTransformation (𝔦₀ A)

        commute : ∀ {Γ Ξ} (f : 𝒲 Ξ Γ) {γ δ : Setoid.Carrier (𝔑𝔣.₀ Δ Γ)} {a b : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)}
                  → Setoid._≈_ (𝔑𝔣.₀ Δ Γ) γ δ
                  → a ≡ b
                  →  (𝔦Δ.η Ξ ⟨$⟩ (𝔑𝔣.₁ Δ f ⟨$⟩ γ)) S.∷ S.𝒵 (𝔦₀A.η Ξ ⟨$⟩ (𝔑𝔣₀.₁ A f ⟨$⟩ a))
                    S.S.≈ Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦Δ.η Γ ⟨$⟩ δ) S.∷ S.𝒵 (𝔦₀A.η Γ ⟨$⟩ b)
        commute {Γ} {Ξ} f {γ} {δ} {a} {b} γ≈δ PE.refl = begin
            (𝔦Δ.η Ξ ⟨$⟩ (𝔑𝔣.₁ Δ f ⟨$⟩ γ)) S.∷ S.𝒵 (𝔦₀A.η Ξ ⟨$⟩ (𝔑𝔣₀.₁ A f ⟨$⟩ a))
          ≈⟨ S.∷-cong₂ (𝔦Δ.commute f γ≈δ) (S.𝒵-cong (𝔦₀A.commute f {b} PE.refl)) ⟩
            (Functor.₁ (Tm.₀ Δ) f ⟨$⟩ (𝔦Δ.η Γ ⟨$⟩ δ)) S.∷ S.𝒵 (Functor.₁ (Tm.₀ (𝟙 · A)) f ⟨$⟩ (𝔦₀A.η Γ ⟨$⟩ a))
          ≈⟨ S.∷-cong₂ (S.S.sym S.πβ) (S.C.trans (S.C.trans S.v𝒵 (S.C.sym (S.sb-comp {γ = 𝔦₀-η A Γ b}))) (S.C.sym S.v𝓏)) ⟩
            Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦Δ.η Γ ⟨$⟩ δ) S.∷ S.𝒵 (𝔦₀A.η Γ ⟨$⟩ a)
          ∎
          where open Reasoning S.S.setoid

𝔦′ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦′ 𝟙       = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = λ _ → S.! ; cong = λ x → S.!η }
  ; commute = λ _ _ → S.!η
  })
𝔦′ (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ Repr.∷ a) → (𝔦′Δ.η Γ ⟨$⟩ γ) S.∷ S.𝒵 (𝔦₀′A.η Γ ⟨$⟩ a) }
    ; cong = λ { (γ Repr.∷ a) → S.∷-cong₂ (cong (𝔦′Δ.η Γ) γ) (S.𝒵-cong (cong (𝔦₀′A.η Γ) a)) }
    }
  ; commute = λ f → λ { (γ Repr.∷ a) → commute f γ a }
  })
  where module 𝔦′Δ = NaturalTransformation (𝔦′ Δ)
        module 𝔦₀′A = NaturalTransformation (𝔦₀′ A)

        commute : ∀ {Γ Ξ} (f : 𝒲 Ξ Γ) {γ δ : Setoid.Carrier (𝔑𝔢.₀ Δ Γ)} {a b : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
                  → Setoid._≈_ (𝔑𝔢.₀ Δ Γ) γ δ
                  → a ≡ b
                  →  (𝔦′Δ.η Ξ ⟨$⟩ (𝔑𝔢.₁ Δ f ⟨$⟩ γ)) S.∷ S.𝒵 (𝔦₀′A.η Ξ ⟨$⟩ (𝔑𝔢₀.₁ A f ⟨$⟩ a))
                    S.S.≈ Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦′Δ.η Γ ⟨$⟩ δ) S.∷ S.𝒵 (𝔦₀′A.η Γ ⟨$⟩ b)
        commute {Γ} {Ξ} f {γ} {δ} {a} {b} γ≈δ PE.refl = begin
            (𝔦′Δ.η Ξ ⟨$⟩ (𝔑𝔢.₁ Δ f ⟨$⟩ γ)) S.∷ S.𝒵 (𝔦₀′A.η Ξ ⟨$⟩ (𝔑𝔢₀.₁ A f ⟨$⟩ a))
          ≈⟨ S.∷-cong₂ (𝔦′Δ.commute f γ≈δ) (S.𝒵-cong (𝔦₀′A.commute f {b} PE.refl)) ⟩
            (Functor.₁ (Tm.₀ Δ) f ⟨$⟩ (𝔦′Δ.η Γ ⟨$⟩ δ)) S.∷ S.𝒵 (Functor.₁ (Tm.₀ (𝟙 · A)) f ⟨$⟩ (𝔦₀′A.η Γ ⟨$⟩ a))
          ≈⟨ S.∷-cong₂ (S.S.sym S.πβ) (S.C.trans (S.C.trans S.v𝒵 (S.C.sym (S.sb-comp {γ = 𝔦₀′-η A Γ b}))) (S.C.sym S.v𝓏)) ⟩
            Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦′Δ.η Γ ⟨$⟩ δ) S.∷ S.𝒵 (𝔦₀′A.η Γ ⟨$⟩ a)
          ∎
          where open Reasoning S.S.setoid

module _ A where module 𝔦₀ = NaturalTransformation (𝔦₀ A)
module _ A where module 𝔦₀′ = NaturalTransformation (𝔦₀′ A)
module _ Γ where module 𝔦 = NaturalTransformation (𝔦 Γ)
module _ Γ where module 𝔦′ = NaturalTransformation (𝔦′ Γ)

Gl : Category (suc a) a a
Gl = Comma {A = Psh.Psh} Categories.Functor.id Tm

module Gl = Category Gl
