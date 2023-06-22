{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Base {a} (𝒰 : Set a) where

open import Level
open import Function.Equality using (_⟨$⟩_; cong)

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
open import TDPE.Gluing.Representation 𝒰 as R using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣)
open import TDPE.Gluing.Syntax 𝒰
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

W = ⟦_⟧ CC

module W = Functor W

Tm : Functor 𝕋𝕞 Psh.Psh
Tm = precompose (Functor.op W) ∘F Yoneda.embed 𝕋𝕞

module Tm = Functor Tm

module _ A where module 𝔑𝔣₀ = Functor (𝔑𝔣₀ A)
module _ A where module 𝔑𝔢₀ = Functor (𝔑𝔢₀ A)
module _ Γ where module 𝔑𝔣 = Functor (𝔑𝔣 Γ)
module _ Γ where module 𝔑𝔢 = Functor (𝔑𝔢 Γ)

private

  𝔦₀-η : ∀ A Γ → Setoid.Carrier (𝔑𝔣₀.₀ A Γ) → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)
  𝔦₀′-η : ∀ A Γ → Setoid.Carrier (𝔑𝔢₀.₀ A Γ) → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)

  𝔦₀-cong : ∀ A Γ {x y : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)} → x ≡ y → 𝔦₀-η A Γ x S.≈ 𝔦₀-η A Γ y
  𝔦₀′-cong : ∀ A Γ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)} → x ≡ y → 𝔦₀′-η A Γ x S.≈ 𝔦₀′-η A Γ y

  𝔦₀-commute : ∀ A {Γ Δ} (f : 𝒲 Δ Γ) {x y : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)}
               → x ≡ y → 𝔦₀-η A Δ (R.+ f x) S.≈ ! ∷ 𝓏 [ 𝔦₀-η A Γ y ∘ W.₁ f ]
  𝔦₀′-commute : ∀ A {Γ Δ} (f : 𝒲 Δ Γ) {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
               → x ≡ y → 𝔦₀′-η A Δ (R.+′ f x) S.≈ ! ∷ 𝓏 [ 𝔦₀′-η A Γ y ∘ W.₁ f ]

  v : ∀ {Γ A} → R.var Γ A → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)
  v R.𝓏     = ! ∷ 𝓏
  v (R.π x) = ! ∷ p (𝒵 (v x))

  𝔦₀-η _       Γ (R.ι x) = 𝔦₀′-η _ Γ x
  𝔦₀-η (A ⇒ B) Γ (R.Λ x) = ! ∷ Λ (𝒵 (𝔦₀-η B (Γ · A) x))

  𝔦₀′-η A Γ (R.𝓋 x)     = v x
  𝔦₀′-η A Γ (f R.⦅ x ⦆) = ! ∷ 𝒵 (𝔦₀′-η _ Γ f) ⦅ 𝒵 (𝔦₀-η _ Γ x) ⦆

  -- NOTE(@doctorn) these proofs could just be done with `Setoid.reflexive`, but I wanted to future proof
  -- them a bit for partial evaluation
  𝔦₀-cong _       Γ {R.ι x} PE.refl = 𝔦₀′-cong _ Γ {x} PE.refl
  𝔦₀-cong (A ⇒ B) Γ {R.Λ x} PE.refl = ∷-congᵣ (Λ-cong (𝒵-cong (𝔦₀-cong B (Γ · A) {x} PE.refl)))

  𝔦₀′-cong A Γ {R.𝓋 x}    PE.refl = Setoid.reflexive (Functor.₀ (Tm.₀ (𝟙 · A)) Γ) PE.refl
  𝔦₀′-cong A Γ {f R.⦅ x ⦆} PE.refl =
    ∷-congᵣ (app-cong₂ (𝒵-cong (𝔦₀′-cong _ Γ {f} PE.refl))
      (𝒵-cong (𝔦₀-cong _ Γ {x} PE.refl)))

  𝔦₀-commute _       f {x = R.ι x} PE.refl = 𝔦₀′-commute _ f {x} PE.refl
  𝔦₀-commute (A ⇒ B) f {x = R.Λ x} PE.refl = ∷-congᵣ (begin
      Λ (𝒵 (𝔦₀-η B _ (R.+ (ω₂ f) x)))
    ≈⟨ Λ-cong (𝒵-cong (𝔦₀-commute B (ω₂ f) {x} PE.refl)) ⟩
      Λ (𝓏 [ 𝔦₀-η B _ x ∘ _ ])
    ≈⟨ Λ-cong v𝒵 ⟩
      Λ (𝒵 (𝔦₀-η B _ x ∘ _))
    ≈⟨ Λ-cong (C.sym (sb-comp {γ = 𝔦₀-η B _ x})) ⟩
      Λ (𝒵 (𝔦₀-η _ _ x) [ _ ])
    ≈⟨ Λ-cong (sb-congᵣ (∷-congₗ (S.trans (S.sym πβ) ∘-identityʳ))) ⟩
      Λ (𝒵 (𝔦₀-η _ _ x) [ _ ])
    ≈⟨ C.sym sb-lam ⟩
      Λ (𝒵 (𝔦₀-η _ _ x)) [ _ ]
    ≈⟨ C.sym v𝓏 ⟩
      𝓏 [ (! ∷ Λ (𝒵 (𝔦₀-η _ _ x))) ∘ _ ]
    ∎)
    where open Reasoning C.setoid

  𝔦₀′-commute A f {R.𝓋 x} PE.refl =
    S.trans (S.trans (I f x) (S.sym 𝒵η)) (∷-congᵣ (C.sym v𝒵))
    where I : ∀ {Γ Δ} (f : 𝒲 Δ Γ) (x : R.var Γ A)
              → v (R.+var f x) S.≈ v x ∘ W.₁ f
          I {Γ · A} {Δ} (ω₁ f) R.𝓏 = ∷-congᵣ (begin
              p (𝒵 (v (R.+var f R.𝓏)))
            ≈⟨ p-cong (𝒵-cong (I f R.𝓏)) ⟩
              p (𝒵 (v (R.𝓏 {Γ = Γ}) ∘ W.₁ f))
            ≈⟨ p-π ⟩
              𝓏 [ π (W.₁ f) ]
            ≈⟨ sb-congᵣ (S.sym π-id) ⟩
              𝓏 [ W.₁ f ∘ π id ]
            ∎)
            where open Reasoning C.setoid
          I {Γ · A} {Δ · A} (ω₂ f) R.𝓏 = S.sym (∷-congᵣ v𝓏)
          I {Γ · A} {Δ} (ω₁ f) (R.π x) = ∷-congᵣ (begin
              p (𝒵 (v (R.+var f (R.π x))))
            ≈⟨ p-cong (𝒵-cong (I f (R.π x))) ⟩
              p (p (𝒵 (v x)) [ W.₁ f ])
            ≈⟨ p-π ⟩
              p (𝒵 (v x)) [ π (W.₁ f) ]
            ≈⟨ sb-congᵣ (S.sym π-id) ⟩
              p (𝒵 (v x)) [ W.₁ f ∘ π id ]
            ∎)
            where open Reasoning C.setoid
          I {Γ · A} {Δ · A} (ω₂ f) (R.π x) = ∷-congᵣ (begin
              p (𝒵 (v (R.+var f x)))
            ≈⟨ p-cong (𝒵-cong (I f x)) ⟩
              p (𝒵 (v x ∘ W.₁ f))
            ≈⟨ 𝒵p {γ = v x ∘ W.₁ f} ⟩
              𝓏 [ π (v x ∘ W.₁ f) ]
            ≈⟨ sb-congᵣ (S.sym π-lemma) ⟩
              𝓏 [ v x ∘ π (W.₁ f) ]
            ≈⟨ C.sym sb-assoc ⟩
              𝓏 [ v x ] [ π (W.₁ f) ]
            ≈⟨ sb-cong₂ v𝒵 (S.sym π-id) ⟩
              𝒵 (v x) [ W.₁ f ∘ π id ]
            ≈⟨ C.sym vp ⟩
              p (𝒵 (v x)) [ W.₁ f ∘ π id ∷ 𝓏 ]
            ∎)
            where open Reasoning C.setoid
  𝔦₀′-commute A f {t R.⦅ x ⦆} PE.refl = ∷-congᵣ (begin
      𝒵 (𝔦₀′-η _ _ (R.+′ f t)) ⦅ 𝒵 (𝔦₀-η _ _ (R.+ f x)) ⦆
    ≈⟨ app-cong₂ (𝒵-cong (𝔦₀′-commute _ f {t} PE.refl)) (𝒵-cong (𝔦₀-commute _ f {x} PE.refl)) ⟩
      𝓏 [ _ ] ⦅ 𝓏 [ _ ] ⦆
    ≈⟨ app-cong₂ v𝒵 v𝒵 ⟩
      _ ⦅ _ ⦆
    ≈⟨ C.sym (app-cong₂ (sb-comp {γ = 𝔦₀′-η _ _ t}) (sb-comp {γ = 𝔦₀-η _ _ x})) ⟩
      _ ⦅ _ ⦆
    ≈⟨ C.sym sb-app ⟩
      (𝒵 (𝔦₀′-η _ _ t) ⦅ 𝒵 (𝔦₀-η _ _ x) ⦆) [ _ ]
    ≈⟨ C.sym v𝓏 ⟩
      𝓏 [ (! ∷ 𝒵 (𝔦₀′-η _ _ t) ⦅ 𝒵 (𝔦₀-η _ _ x) ⦆) ∘ _ ]
    ∎)
    where open Reasoning C.setoid

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
  { η = λ Γ → record { _⟨$⟩_ = λ _ → ! ; cong = λ _ → !η }
  ; commute = λ _ _ → !η
  })
𝔦 (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ R.∷ a) → (𝔦Δ.η Γ ⟨$⟩ γ) ∷ 𝒵 (𝔦₀A.η Γ ⟨$⟩ a) }
    ; cong = λ { (γ R.∷ a) → ∷-cong₂ (cong (𝔦Δ.η Γ) γ) (𝒵-cong (cong (𝔦₀A.η Γ) a)) }
    }
  ; commute = λ f → λ { (γ R.∷ a) → commute f γ a }
  })
  where module 𝔦Δ = NaturalTransformation (𝔦 Δ)
        module 𝔦₀A = NaturalTransformation (𝔦₀ A)

        commute : ∀ {Γ Ξ} (f : 𝒲 Ξ Γ) {γ δ : Setoid.Carrier (𝔑𝔣.₀ Δ Γ)} {a b : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)}
                  → Setoid._≈_ (𝔑𝔣.₀ Δ Γ) γ δ
                  → a ≡ b
                  →  (𝔦Δ.η Ξ ⟨$⟩ (𝔑𝔣.₁ Δ f ⟨$⟩ γ)) ∷ 𝒵 (𝔦₀A.η Ξ ⟨$⟩ (𝔑𝔣₀.₁ A f ⟨$⟩ a))
                    S.≈ Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦Δ.η Γ ⟨$⟩ δ) ∷ 𝒵 (𝔦₀A.η Γ ⟨$⟩ b)
        commute {Γ} {Ξ} f {γ} {δ} {a} {b} γ≈δ PE.refl = begin
            (𝔦Δ.η Ξ ⟨$⟩ (𝔑𝔣.₁ Δ f ⟨$⟩ γ)) ∷ 𝒵 (𝔦₀A.η Ξ ⟨$⟩ (𝔑𝔣₀.₁ A f ⟨$⟩ a))
          ≈⟨ ∷-cong₂ (𝔦Δ.commute f γ≈δ) (𝒵-cong (𝔦₀A.commute f {b} PE.refl)) ⟩
            (Functor.₁ (Tm.₀ Δ) f ⟨$⟩ (𝔦Δ.η Γ ⟨$⟩ δ)) ∷ 𝒵 (Functor.₁ (Tm.₀ (𝟙 · A)) f ⟨$⟩ (𝔦₀A.η Γ ⟨$⟩ a))
          ≈⟨ ∷-cong₂ (S.sym πβ) (C.trans (C.trans v𝒵 (C.sym (sb-comp {γ = 𝔦₀-η A Γ b}))) (C.sym v𝓏)) ⟩
            Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦Δ.η Γ ⟨$⟩ δ) ∷ 𝒵 (𝔦₀A.η Γ ⟨$⟩ a)
          ∎
          where open Reasoning S.setoid

𝔦′ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦′ 𝟙       = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = λ _ → ! ; cong = λ x → !η }
  ; commute = λ _ _ → !η
  })
𝔦′ (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ R.∷ a) → (𝔦′Δ.η Γ ⟨$⟩ γ) ∷ 𝒵 (𝔦₀′A.η Γ ⟨$⟩ a) }
    ; cong = λ { (γ R.∷ a) → ∷-cong₂ (cong (𝔦′Δ.η Γ) γ) (𝒵-cong (cong (𝔦₀′A.η Γ) a)) }
    }
  ; commute = λ f → λ { (γ R.∷ a) → commute f γ a }
  })
  where module 𝔦′Δ = NaturalTransformation (𝔦′ Δ)
        module 𝔦₀′A = NaturalTransformation (𝔦₀′ A)

        commute : ∀ {Γ Ξ} (f : 𝒲 Ξ Γ) {γ δ : Setoid.Carrier (𝔑𝔢.₀ Δ Γ)} {a b : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
                  → Setoid._≈_ (𝔑𝔢.₀ Δ Γ) γ δ
                  → a ≡ b
                  →  (𝔦′Δ.η Ξ ⟨$⟩ (𝔑𝔢.₁ Δ f ⟨$⟩ γ)) ∷ 𝒵 (𝔦₀′A.η Ξ ⟨$⟩ (𝔑𝔢₀.₁ A f ⟨$⟩ a))
                    S.≈ Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦′Δ.η Γ ⟨$⟩ δ) ∷ 𝒵 (𝔦₀′A.η Γ ⟨$⟩ b)
        commute {Γ} {Ξ} f {γ} {δ} {a} {b} γ≈δ PE.refl = begin
            (𝔦′Δ.η Ξ ⟨$⟩ (𝔑𝔢.₁ Δ f ⟨$⟩ γ)) ∷ 𝒵 (𝔦₀′A.η Ξ ⟨$⟩ (𝔑𝔢₀.₁ A f ⟨$⟩ a))
          ≈⟨ ∷-cong₂ (𝔦′Δ.commute f γ≈δ) (𝒵-cong (𝔦₀′A.commute f {b} PE.refl)) ⟩
            (Functor.₁ (Tm.₀ Δ) f ⟨$⟩ (𝔦′Δ.η Γ ⟨$⟩ δ)) ∷ 𝒵 (Functor.₁ (Tm.₀ (𝟙 · A)) f ⟨$⟩ (𝔦₀′A.η Γ ⟨$⟩ a))
          ≈⟨ ∷-cong₂ (S.sym πβ) (C.trans (C.trans v𝒵 (C.sym (sb-comp {γ = 𝔦₀′-η A Γ b}))) (C.sym v𝓏)) ⟩
            Functor.₁ (Tm.₀ (Δ · A)) f ⟨$⟩ (𝔦′Δ.η Γ ⟨$⟩ δ) ∷ 𝒵 (𝔦₀′A.η Γ ⟨$⟩ a)
          ∎
          where open Reasoning S.setoid

module _ A where module 𝔦₀ = NaturalTransformation (𝔦₀ A)
module _ A where module 𝔦₀′ = NaturalTransformation (𝔦₀′ A)
module _ Γ where module 𝔦 = NaturalTransformation (𝔦 Γ)
module _ Γ where module 𝔦′ = NaturalTransformation (𝔦′ Γ)

Gl : Category (suc a) a a
Gl = Comma {A = Psh.Psh} Categories.Functor.id Tm

module Gl = Category Gl
