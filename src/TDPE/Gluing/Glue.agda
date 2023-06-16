{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)
open import Categories.Yoneda

open import TDPE.Gluing.Categories.Functor.Properties using (precompose)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ⟦_⟧; ω₁; ω₂)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Representation 𝒰 as Repr
  using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣; 𝓋; 𝓏; π; ι; Λ; _⦅_⦆)
import TDPE.Gluing.Syntax 𝒰 as Syn
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

Tm : Functor Syn.𝕋𝕞 Psh.Psh
Tm = precompose (Functor.op (⟦_⟧ Syn.CC)) ∘F Yoneda.embed Syn.𝕋𝕞

module Tm = Functor Tm

Gl : Category (suc a) a a
Gl = Comma {A = Psh.Psh} Categories.Functor.id Tm

𝓡₀ : 𝒰ᵀ → Psh.Obj
𝓡₀ A = ⟦ A ⟧ᵀ (λ A₀ → 𝔑𝔣₀ ` A₀ `) Psh._^′_

𝓡 : ℭ → Psh.Obj
𝓡 Γ = ⟦ Γ ⟧ᶜ (λ A₀ → 𝔑𝔣₀ ` A₀ `) Psh._^′_ Psh.⊤′ Psh._·′_

module 𝕎 = Category 𝕎
module _ (A : 𝒰ᵀ) where module 𝔑𝔣₀ = Functor (𝔑𝔣₀ A)
module _ (A : 𝒰ᵀ) where module 𝔑𝔢₀ = Functor (𝔑𝔢₀ A)
module _ (A : 𝒰ᵀ) where module 𝓡₀ = Functor (𝓡₀ A)
module _ (Γ : ℭ) where module 𝔑𝔣 = Functor (𝔑𝔣 Γ)
module _ (Γ : ℭ) where module 𝔑𝔢 = Functor (𝔑𝔢 Γ)
module _ (Γ : ℭ) where module 𝓡 = Functor (𝓡 Γ)

private
  ↑₀-η : ∀ A Δ → Setoid.Carrier (𝓡₀.₀ A Δ) → Setoid.Carrier (𝔑𝔣₀.₀ A Δ)
  ↓₀-η : ∀ A Δ → Setoid.Carrier (𝔑𝔢₀.₀ A Δ) → Setoid.Carrier (𝓡₀.₀ A Δ)

  ↑₀-cong : ∀ A Δ {x y : Setoid.Carrier (𝓡₀.₀ A Δ)}
            → Setoid._≈_ (𝓡₀.₀ A Δ) x y
            → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↑₀-η A Δ x) (↑₀-η A Δ y)
  ↓₀-cong : ∀ A Δ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Δ)}
            → Setoid._≈_ (𝔑𝔢₀.₀ A Δ) x y
            → Setoid._≈_ (𝓡₀.₀ A Δ) (↓₀-η A Δ x) (↓₀-η A Δ y)

  ↑₀-commute : ∀ A {Γ Δ} (w : 𝕎 [ Δ , Γ ])
               → ∀ {x y : Setoid.Carrier (𝓡₀.₀ A Γ)}
               → Setoid._≈_ (𝓡₀.₀ A Γ) x y
               → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↑₀-η A Δ (𝓡₀.₁ A w ⟨$⟩ x)) (Repr.+ w (↑₀-η A Γ y))
  ↓₀-commute : ∀ A {Γ Δ} (w : 𝕎 [ Δ , Γ ])
               → ∀ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
               → Setoid._≈_ (𝔑𝔢₀.₀ A Γ) x y
               → Setoid._≈_ (𝓡₀.₀ A Δ) (↓₀-η A Δ (Repr.+′ w x)) (𝓡₀.₁ A w ⟨$⟩ ↓₀-η A Γ y)

  ↑₀-η ` A `   Δ x = x
  ↑₀-η (A ⇒ B) Δ x = Λ (↑₀-η B (Δ · A) (proj₂ (x.η (Δ · A) ⟨$⟩ (↓₀-η A (Δ · A) (𝓋 𝓏) , ω₁ 𝕎.id))))
    where module x = NaturalTransformation x

  ↑₀-cong ` A `   Δ x = x
  ↑₀-cong (A ⇒ B) Δ x =
    PE.cong Λ (↑₀-cong B (Δ · A) (proj₂ (x (↓₀-cong A (Δ · A) PE.refl , PE.refl))))

  ↑₀-commute ` A `   w x = cong (𝓡₀.₁ ` A ` w) x
  ↑₀-commute (A ⇒ B) {Γ} {Δ} w {x₁} {x₂} x₁≈x₂ = begin
      Λ (↑₀-η B (Δ · A) (proj₂ (x₁.η (Δ · A) ⟨$⟩ (↓₀-η A (Δ · A) (𝓋 𝓏) , w 𝕎.∘ ω₁ 𝕎.id))))
    ≡⟨ PE.cong Λ (↑₀-cong B (Δ · A) (proj₂ (cong (x₁.η (Δ · A)) (↓₀-commute A (ω₂ w) PE.refl , PE.refl)))) ⟩
      Λ (↑₀-η B (Δ · A) (proj₂ (x₁.η (Δ · A) ⟨$⟩ (𝓡₀.₁ A (ω₂ w) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏)) , w 𝕎.∘ ω₁ 𝕎.id))))
    ≡⟨ PE.cong Λ (↑₀-cong B (Δ · A) (proj₂ (x₁≈x₂ (Setoid.refl (𝓡₀.₀ A (Δ · A)) , PE.cong ω₁ I)))) ⟩
      Λ (↑₀-η B (Δ · A) (proj₂ (x₂.η (Δ · A) ⟨$⟩ (Functor.₁ (𝓡₀ A Psh.·′ Psh.𝕪.₀ Γ) (ω₂ w) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ≡⟨
      PE.cong Λ
        (↑₀-cong B (Δ · A) (NaturalTransformation.commute (Psh.↓ Psh.∘ x₂) (ω₂ w)
          (Setoid.refl (𝓡₀.₀ A (Γ · A)) , PE.refl)))
    ⟩
      Λ (↑₀-η B (Δ · A) (𝓡₀.₁ B (ω₂ w) ⟨$⟩ (proj₂ (x₂.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ≡⟨ PE.cong Λ (↑₀-commute B (ω₂ w) (Setoid.refl (𝓡₀.₀ B (Γ · A)))) ⟩
      Λ (Repr.+ (ω₂ w) (↑₀-η B (Γ · A) (proj₂ (x₂.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ≡⟨⟩
      Repr.+ w (Λ (↑₀-η B (Γ · A) (proj₂ (x₂.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ∎
    where open PE.≡-Reasoning
          module x₁ = NaturalTransformation x₁
          module x₂ = NaturalTransformation x₂

          I : w 𝕎.∘ 𝕎.id ≡ 𝕎.id 𝕎.∘ (𝕎.id 𝕎.∘ w)
          I = begin
              w 𝕎.∘ 𝕎.id
            ≡⟨ 𝕎.identityʳ ⟩
              w
            ≡⟨ PE.sym 𝕎.identityˡ ⟩
              𝕎.id 𝕎.∘ w
            ≡⟨ PE.sym 𝕎.identityˡ ⟩
              𝕎.id 𝕎.∘ (𝕎.id 𝕎.∘ w)
            ∎

  ↓₀-η ` A `   Δ x = ι x
  ↓₀-η (A ⇒ B) Δ x = ntHelper (record
    { η = λ Γ → record
      { _⟨$⟩_ = λ e → tt , ↓₀-η B Γ (Repr.+′ (proj₂ e) x ⦅ ↑₀-η A Γ (proj₁ e) ⦆)
      ; cong = λ e → tt , ↓₀-cong B Γ
        (PE.cong₂ _⦅_⦆ (PE.cong₂ Repr.+′ (proj₂ e) PE.refl) (↑₀-cong A Γ (proj₁ e)))
      }
    ; commute = λ {Γ} {Δ} f →
      λ { {y₁ , w} {y₂ , _} (y₁≈y₂ , PE.refl)
        → tt , Setoid.trans (𝓡₀.₀ B Δ)
          (↓₀-cong B Δ
            (PE.cong₂ _⦅_⦆
              (PE.trans
                  (PE.cong₂ Repr.+′ 𝕎.identityˡ PE.refl)
                  (Repr.+′-homomorphism PE.refl)
              )
              (↑₀-commute A f (Setoid.refl (𝓡₀.₀ A Γ)))
            )
          )
          (↓₀-commute B f (PE.cong₂ _⦅_⦆ PE.refl (↑₀-cong A Γ y₁≈y₂)))
      }
    })

  ↓₀-cong ` A `   Δ x = PE.cong ι x
  ↓₀-cong (A ⇒ B) Δ x {Γ} (y , w) =
    tt , ↓₀-cong B Γ (PE.cong₂ _⦅_⦆ (PE.cong₂ Repr.+′ w x) (↑₀-cong A Γ y))

  ↓₀-commute ` A `   w x = PE.cong ι (PE.cong (Repr.+′ w) x)
  ↓₀-commute (A ⇒ B) w PE.refl {Ξ} (y₁≈y₂ , PE.refl) =
    tt , ↓₀-cong B Ξ (PE.cong₂ _⦅_⦆ (PE.sym (Repr.+′-homomorphism PE.refl)) (↑₀-cong A Ξ y₁≈y₂))

↑₀ : ∀ A → 𝓡₀ A Psh.⇒ 𝔑𝔣₀ A
↑₀ A = ntHelper (record
  { η = λ Δ → record
    { _⟨$⟩_ = ↑₀-η A Δ
    ; cong = ↑₀-cong A Δ
    }
  ; commute = ↑₀-commute A
  })

↓₀ : ∀ A → 𝔑𝔢₀ A Psh.⇒ 𝓡₀ A
↓₀ A = ntHelper (record
  { η = λ Δ → record
    { _⟨$⟩_ = ↓₀-η A Δ
    ; cong = ↓₀-cong A Δ
    }
  ; commute = ↓₀-commute A
  })

↑ : ∀ Δ → 𝓡 Δ Psh.⇒ 𝔑𝔣 Δ
↑ 𝟙 = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ _ → Repr.!
    ; cong = λ _ → Repr.!
    }
  ; commute = λ _ _ → Repr.!
  })
↑ (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ x → (↑Δ.η Γ ⟨$⟩ proj₁ x) Repr.∷ ↑₀-η A Γ (proj₂ x)
    ; cong = λ x → cong (↑Δ.η Γ) (proj₁ x) Repr.∷ ↑₀-cong A Γ (proj₂ x)
    }
  ; commute = λ f x → ↑Δ.commute f (proj₁ x) Repr.∷ ↑₀-commute A f (proj₂ x)
  })
  where module ↑Δ = NaturalTransformation (↑ Δ)

↓ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ 𝓡 Δ
↓ 𝟙       = Psh.!
↓ (Δ · A) = Psh.⟨ ↓ Δ Psh.∘ Repr.proj 𝔑𝔢₀ , Psh.↑ Psh.∘ ↓₀ A Psh.∘ Repr.zero′ 𝔑𝔢₀ ⟩

private

  𝔦₀-η : ∀ A Γ → Setoid.Carrier (𝔑𝔣₀.₀ A Γ) → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)
  𝔦₀′-η : ∀ A Γ → Setoid.Carrier (𝔑𝔢₀.₀ A Γ) → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)

  𝔦₀-cong : ∀ A Γ {x y : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)} → x ≡ y → 𝔦₀-η A Γ x Syn.S.≈ 𝔦₀-η A Γ y
  𝔦₀′-cong : ∀ A Γ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)} → x ≡ y → 𝔦₀′-η A Γ x Syn.S.≈ 𝔦₀′-η A Γ y

  𝔦₀-commute : ∀ A {Γ Δ} (f : 𝕎 [ Δ , Γ ]) {x y : Setoid.Carrier (𝔑𝔣₀.₀ A Γ)}
               → x ≡ y → 𝔦₀-η A Δ (Repr.+ f x) Syn.S.≈ Syn.! Syn.∷ Syn.𝓏 Syn.[ 𝔦₀-η A Γ y Syn.∘ (Functor.₁ (⟦_⟧ Syn.CC) f) ]
  𝔦₀′-commute : ∀ A {Γ Δ} (f : 𝕎 [ Δ , Γ ]) {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
               → x ≡ y → 𝔦₀′-η A Δ (Repr.+′ f x) Syn.S.≈ Syn.! Syn.∷ Syn.𝓏 Syn.[ 𝔦₀′-η A Γ y Syn.∘ (Functor.₁ (⟦_⟧ Syn.CC) f) ]

  v : ∀ {Γ A} → Repr.var Γ A → Setoid.Carrier (Functor.₀ (Tm.₀ (𝟙 · A)) Γ)
  v 𝓏     = Syn.! Syn.∷ Syn.𝓏
  v (π x) = Syn.! Syn.∷ Syn.p (Syn.𝒵 (v x))

  𝔦₀-η _       Γ (ι x) = 𝔦₀′-η _ Γ x
  𝔦₀-η (A ⇒ B) Γ (Λ x) = Syn.! Syn.∷ Syn.Λ (Syn.𝒵 (𝔦₀-η B (Γ · A) x))

  𝔦₀′-η A Γ (𝓋 x)     = v x
  𝔦₀′-η A Γ (f ⦅ x ⦆) = Syn.! Syn.∷ Syn.𝒵 (𝔦₀′-η _ Γ f) Syn.⦅ Syn.𝒵 (𝔦₀-η _ Γ x) ⦆

  -- NOTE(@doctorn) these proofs could just be done with `Setoid.reflexive`, but I wanted to future proof
  -- them a bit for partial evaluation
  𝔦₀-cong _       Γ {ι x} PE.refl = 𝔦₀′-cong _ Γ {x} PE.refl
  𝔦₀-cong (A ⇒ B) Γ {Λ x} PE.refl = Syn.∷-congᵣ (Syn.Λ-cong (Syn.𝒵-cong (𝔦₀-cong B (Γ · A) {x} PE.refl)))

  𝔦₀′-cong A Γ {𝓋 x}    PE.refl = Setoid.reflexive (Functor.₀ (Tm.₀ (𝟙 · A)) Γ) PE.refl
  𝔦₀′-cong A Γ {f ⦅ x ⦆} PE.refl =
    Syn.∷-congᵣ (Syn.app-cong₂ (Syn.𝒵-cong (𝔦₀′-cong _ Γ {f} PE.refl))
      (Syn.𝒵-cong (𝔦₀-cong _ Γ {x} PE.refl)))

  𝔦₀-commute _       f {x = ι x} PE.refl = 𝔦₀′-commute _ f {x} PE.refl
  𝔦₀-commute (A ⇒ B) f {x = Λ x} PE.refl = Syn.∷-congᵣ (begin
      Syn.Λ (Syn.𝒵 (𝔦₀-η B _ (Repr.+ (ω₂ f) x)))
    ≈⟨ Syn.Λ-cong (Syn.𝒵-cong (𝔦₀-commute B (ω₂ f) {x} PE.refl)) ⟩
      Syn.Λ (Syn.𝓏 Syn.[ 𝔦₀-η B _ x Syn.∘ _ ])
    ≈⟨ Syn.Λ-cong Syn.v𝒵 ⟩
      Syn.Λ (Syn.𝒵 (𝔦₀-η B _ x Syn.∘ _))
    ≈⟨ Syn.Λ-cong (Syn.C.sym (Syn.sb-comp {γ = 𝔦₀-η B _ x})) ⟩
      Syn.Λ (Syn.𝒵 (𝔦₀-η _ _ x) Syn.[ _ ])
    ≈⟨ Syn.Λ-cong (Syn.sb-congᵣ (Syn.∷-congₗ (Syn.S.trans (Syn.S.sym Syn.πβ) Syn.∘-identityʳ))) ⟩
      Syn.Λ (Syn.𝒵 (𝔦₀-η _ _ x) Syn.[ _ ])
    ≈⟨ Syn.C.sym Syn.sb-lam ⟩
      Syn.Λ (Syn.𝒵 (𝔦₀-η _ _ x)) Syn.[ _ ]
    ≈⟨ Syn.C.sym Syn.v𝓏 ⟩
      Syn.𝓏 Syn.[ (Syn.! Syn.∷ Syn.Λ (Syn.𝒵 (𝔦₀-η _ _ x))) Syn.∘ _ ]
    ∎)
    where open Reasoning Syn.C.setoid

  𝔦₀′-commute A f {𝓋 x} PE.refl =
    Syn.S.trans (Syn.S.trans (I f x) (Syn.S.sym Syn.𝒵η)) (Syn.∷-congᵣ (Syn.C.sym Syn.v𝒵))
    where I : ∀ {Γ Δ} (f : 𝕎 [ Δ , Γ ]) (x : Repr.var Γ A)
              → v (Repr.+var f x) Syn.S.≈ v x Syn.∘ (Functor.₁ (⟦_⟧ Syn.CC) f)
          I {Γ · A} {Δ} (ω₁ f) 𝓏 = Syn.∷-congᵣ (begin
              Syn.p (Syn.𝒵 (v (Repr.+var f 𝓏)))
            ≈⟨ Syn.p-cong (Syn.𝒵-cong (I f 𝓏)) ⟩
              Syn.p (Syn.𝒵 (v (𝓏 {Γ = Γ}) Syn.∘ (Functor.₁ (⟦_⟧ Syn.CC) f)))
            ≈⟨ Syn.p-π ⟩
              Syn.𝓏 Syn.[ Syn.π (Functor.₁ (⟦_⟧ Syn.CC) f) ]
            ≈⟨ Syn.sb-congᵣ (Syn.S.sym (Syn.S.trans Syn.π-lemma (Syn.π-cong Syn.∘-identityʳ))) ⟩
              Syn.𝓏 Syn.[ Functor.₁ (⟦_⟧ Syn.CC) f Syn.∘ Syn.π Syn.id ]
            ∎)
            where open Reasoning Syn.C.setoid
          I {Γ · A} {Δ · A} (ω₂ f) 𝓏 = Syn.S.sym (Syn.∷-congᵣ Syn.v𝓏)
          I {Γ · A} {Δ} (ω₁ f) (π x) = Syn.∷-congᵣ (begin
              Syn.p (Syn.𝒵 (v (Repr.+var f (π x))))
            ≈⟨ Syn.p-cong (Syn.𝒵-cong (I f (π x))) ⟩
              Syn.p (Syn.p (Syn.𝒵 (v x)) Syn.[ Functor.₁ (⟦_⟧ Syn.CC) f ])
            ≈⟨ Syn.p-π ⟩
              Syn.p (Syn.𝒵 (v x)) Syn.[ Syn.π (Functor.₁ (⟦_⟧ Syn.CC) f) ]
            ≈⟨ Syn.sb-congᵣ (Syn.S.sym (Syn.S.trans Syn.π-lemma (Syn.π-cong Syn.∘-identityʳ))) ⟩
              Syn.p (Syn.𝒵 (v x)) Syn.[ Functor.₁ (⟦_⟧ Syn.CC) f Syn.∘ Syn.π Syn.id ]
            ∎)
            where open Reasoning Syn.C.setoid
          I {Γ · A} {Δ · A} (ω₂ f) (π x) = Syn.∷-congᵣ (begin
              Syn.p (Syn.𝒵 (v (Repr.+var f x)))
            ≈⟨ Syn.p-cong (Syn.𝒵-cong (I f x)) ⟩
              Syn.p (Syn.𝒵 (v x Syn.∘ Functor.₁ (⟦_⟧ Syn.CC) f))
            ≈⟨ Syn.𝒵p {γ = v x Syn.∘ Functor.₁ (⟦_⟧ Syn.CC) f} ⟩
              Syn.𝓏 Syn.[ Syn.π (v x Syn.∘ Functor.₁ ⟦ Syn.CC ⟧ f) ]
            ≈⟨ Syn.sb-congᵣ (Syn.S.sym Syn.π-lemma) ⟩
              Syn.𝓏 Syn.[ v x Syn.∘ Syn.π (Functor.₁ ⟦ Syn.CC ⟧ f) ]
            ≈⟨ Syn.C.sym Syn.sb-assoc ⟩
              Syn.𝓏 Syn.[ v x ] Syn.[ Syn.π (Functor.₁ ⟦ Syn.CC ⟧ f) ]
            ≈⟨ Syn.sb-cong₂ Syn.v𝒵 (Syn.S.sym (Syn.S.trans Syn.π-lemma (Syn.π-cong Syn.∘-identityʳ))) ⟩
              Syn.𝒵 (v x) Syn.[ Functor.₁ (⟦_⟧ Syn.CC) f Syn.∘ Syn.π Syn.id ]
            ≈⟨ Syn.C.sym Syn.vp ⟩
              Syn.p (Syn.𝒵 (v x)) Syn.[ Functor.₁ (⟦_⟧ Syn.CC) f Syn.∘ Syn.π Syn.id Syn.∷ Syn.𝓏 ]
            ∎)
            where open Reasoning Syn.C.setoid
  𝔦₀′-commute A f {t ⦅ x ⦆} PE.refl = Syn.∷-congᵣ (begin
      Syn.𝒵 (𝔦₀′-η _ _ (Repr.+′ f t)) Syn.⦅ Syn.𝒵 (𝔦₀-η _ _ (Repr.+ f x)) ⦆
    ≈⟨ Syn.app-cong₂ (Syn.𝒵-cong (𝔦₀′-commute _ f {t} PE.refl)) (Syn.𝒵-cong (𝔦₀-commute _ f {x} PE.refl)) ⟩
      Syn.𝓏 Syn.[ _ ] Syn.⦅ Syn.𝓏 Syn.[ _ ] ⦆
    ≈⟨ Syn.app-cong₂ Syn.v𝒵 Syn.v𝒵 ⟩
      _ Syn.⦅ _ ⦆
    ≈⟨ Syn.C.sym (Syn.app-cong₂ (Syn.sb-comp {γ = 𝔦₀′-η _ _ t}) (Syn.sb-comp {γ = 𝔦₀-η _ _ x})) ⟩
      _ Syn.⦅ _ ⦆
    ≈⟨ Syn.C.sym Syn.sb-app ⟩
      (Syn.𝒵 (𝔦₀′-η _ _ t) Syn.⦅ Syn.𝒵 (𝔦₀-η _ _ x) ⦆) Syn.[ _ ]
    ≈⟨ Syn.C.sym Syn.v𝓏 ⟩
      Syn.𝓏 Syn.[ (Syn.! Syn.∷ Syn.𝒵 (𝔦₀′-η _ _ t) Syn.⦅ Syn.𝒵 (𝔦₀-η _ _ x) ⦆) Syn.∘ _ ]
    ∎)
    where open Reasoning Syn.C.setoid

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

𝔦 : ∀ Δ → 𝔑𝔣 Δ Psh.⇒ Tm.₀ Δ
𝔦 𝟙       = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = λ _ → Syn.! ; cong = λ _ → Syn.!η }
  ; commute = λ _ _ → Syn.!η
  })
𝔦 (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ Repr.∷ a) → (𝔦Δ.η Γ ⟨$⟩ γ) Syn.∷ Syn.𝒵 (𝔦₀A.η Γ ⟨$⟩ a) }
    ; cong = λ { (γ Repr.∷ a) → Syn.∷-cong₂ (cong (𝔦Δ.η Γ) γ) (Syn.𝒵-cong (cong (𝔦₀A.η Γ) a)) }
    }
  ; commute = {!!}
  })
  where module 𝔦Δ = NaturalTransformation (𝔦 Δ)
        module 𝔦₀A = NaturalTransformation (𝔦₀ A)

𝔦′ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦′ 𝟙       = ntHelper (record
  { η = λ Γ → record { _⟨$⟩_ = λ _ → Syn.! ; cong = λ x → Syn.!η }
  ; commute = λ _ _ → Syn.!η
  })
𝔦′ (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ Repr.∷ a) → (𝔦′Δ.η Γ ⟨$⟩ γ) Syn.∷ Syn.𝒵 (𝔦₀′A.η Γ ⟨$⟩ a) }
    ; cong = λ { (γ Repr.∷ a) → Syn.∷-cong₂ (cong (𝔦′Δ.η Γ) γ) (Syn.𝒵-cong (cong (𝔦₀′A.η Γ) a)) }
    }
  ; commute = {!!}
  })
  where module 𝔦′Δ = NaturalTransformation (𝔦′ Δ)
        module 𝔦₀′A = NaturalTransformation (𝔦₀′ A)

𝔮 : ∀ Δ → 𝓡 Δ Psh.⇒ Functor.₀ Tm Δ
𝔮 Δ = 𝔦 Δ Psh.∘ ↑ Δ

yoga₀ : ∀ {A} → 𝔦₀ A Psh.∘ ↑₀ A Psh.∘ ↓₀ A Psh.≈ 𝔦₀′ A
yoga₀ {A = ` A `} PE.refl = Syn.S.refl
yoga₀ {A = A ⇒ B} {Γ} {x} {_} PE.refl =
  Syn.S.trans
    (Syn.∷-congᵣ (Syn.Λ-cong I))
    (Syn.S.sym (ContextualCartesianClosed.η Syn.CCC (𝔦₀′-η (A ⇒ B) Γ x)))
  where open Reasoning Syn.C.setoid

        I = begin
            Syn.𝒵 (𝔦₀-η B (Γ · A) (↑₀-η B (Γ · A) (↓₀-η B (Γ · A) (Repr.+′ (ω₁ (𝕎.id)) x ⦅ ↑₀-η A (Γ · A) (↓₀-η A (Γ · A) (𝓋 𝓏)) ⦆))))
          ≈⟨ Syn.𝒵-cong (yoga₀ PE.refl) ⟩
            Syn.𝒵 (𝔦₀′-η B (Γ · A) (Repr.+′ (ω₁ (𝕎.id)) x ⦅ ↑₀-η A (Γ · A) (↓₀-η A (Γ · A) (𝓋 𝓏)) ⦆))
          ≈⟨ Syn.app-congᵣ (Syn.𝒵-cong (yoga₀ PE.refl)) ⟩
            Syn.𝒵 (𝔦₀′-η (A ⇒ B) (Γ · A) (Repr.+′ (ω₁ 𝕎.id) x)) Syn.⦅ Syn.𝓏 ⦆
          ≈⟨ Syn.app-congₗ (Syn.𝒵-cong (NaturalTransformation.commute (𝔦₀′ (A ⇒ B)) (ω₁ (𝕎.id {Γ})) {x = x} PE.refl)) ⟩
            Syn.𝓏 Syn.[ 𝔦₀′-η (A ⇒ B) Γ x Syn.∘ (Functor.₁ (⟦_⟧ Syn.CC) (𝕎.id {Γ}) Syn.∘ ContextualCartesian.π Syn.CC) ] Syn.⦅ Syn.𝓏 ⦆
          ≈⟨ Syn.app-congₗ (Syn.sb-congᵣ (Syn.∘-congᵣ (Syn.∘-congₗ (Functor.identity (⟦_⟧ Syn.CC) {Γ})))) ⟩
            Syn.𝓏 Syn.[ 𝔦₀′-η (A ⇒ B) Γ x Syn.∘ (Syn.id Syn.∘ ContextualCartesian.π Syn.CC) ] Syn.⦅ Syn.𝓏 ⦆
          ≈⟨ Syn.app-congₗ (Syn.sb-congᵣ (Syn.∘-congᵣ Syn.∘-identityˡ)) ⟩
            Syn.𝓏 Syn.[ 𝔦₀′-η (A ⇒ B) Γ x Syn.∘ Syn.π Syn.id ] Syn.⦅ Syn.𝓏 ⦆
          ≈⟨ Syn.C.sym (Syn.app-cong₂ Syn.vp Syn.v𝓏) ⟩
            (Syn.p Syn.𝓏 Syn.[ _ Syn.∷ Syn.𝓏 ]) Syn.⦅ Syn.𝓏 Syn.[ _ Syn.∷ Syn.𝓏 ] ⦆
          ≈⟨ Syn.C.sym Syn.sb-app ⟩
            (Syn.p Syn.𝓏 Syn.⦅ Syn.𝓏 ⦆) Syn.[ _ Syn.∷ Syn.𝓏 ]
          ∎

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↑ Δ Psh.∘ ↓ Δ Psh.≈ 𝔦′ Δ
yoga {Δ = 𝟙}     Repr.!       = Syn.!η
yoga {Δ = Δ · A} (γ Repr.∷ a) = Syn.∷-cong₂ (yoga γ) (Syn.𝒵-cong (yoga₀ a))

{-
CC : ContextualCartesian Gl 𝒰ᵀ
CC = record
  { terminal = record
    { ⊤ = record
      { α = 𝓡 𝟙
      ; β = 𝟙
      ; f = ntHelper (record
        { η = λ X → record
          { _⟨$⟩_ = λ _ → Syn.!
          ; cong = λ _ → Syn.!η
          }
        ; commute = λ _ _ → Syn.!η
        })
      }
    ; ⊤-is-terminal = record
      { ! = record
        { g = Psh.!
        ; h = Syn.!
        ; commute = λ _ → Syn.!η
        }
      ; !-unique = λ f → Psh.!-unique (Comma⇒.g f) , Syn.S.sym Syn.!η
      }
    }
  ; _·_ = λ Γ A → record
    { α = CommaObj.α Γ Psh.·′ 𝓡₀ A
    ; β = CommaObj.β Γ · A
    ; f = ntHelper (record
      { η = λ X → record
        { _⟨$⟩_ = λ x →
          (NaturalTransformation.η (CommaObj.f Γ) X ⟨$⟩ proj₁ x)
            Syn.∷ Syn.𝒵 (NaturalTransformation.η (𝔮 (𝟙 · A)) X ⟨$⟩ (tt , proj₂ x))
        ; cong = λ x≈y →
          Syn.∷-cong₂ (cong (NaturalTransformation.η (CommaObj.f Γ) X) (proj₁ x≈y))
                      (Syn.𝒵-cong (cong (NaturalTransformation.η (𝔮 (𝟙 · A)) X) (tt , proj₂ x≈y)))
        }
      ; commute = λ f x → {!!}
      })
    }
  ; π = record
    { g = Psh.π
    ; h = Syn.π Syn.id
    ; commute = {!!}
    }
  ; 𝓏 = record
    { g = Psh.𝓏
    ; h = Syn.! Syn.∷ Syn.𝓏
    ; commute = {!!}
    }
  ; extensions = record
    { ⟨_,_⟩ = λ γ a → record
      { g = Psh.⟨ Comma⇒.g γ , Comma⇒.g a ⟩
      ; h = Comma⇒.h γ Syn.∷ Syn.𝒵 (Comma⇒.h a)
      ; commute = {!!}
      }
    ; project₁ = {!!}
    ; project₂ = {!!}
    ; unique = {!!}
    }
  }

CCC : ContextualCartesianClosed Gl 𝒰
CCC = {!!}
-}
