{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)
open import Categories.Yoneda

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

Gl : Category (suc a) a a
Gl = Comma {A = Psh.Psh} Categories.Functor.id Tm

module Gl = Category Gl

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

  ↑₀-commute : ∀ A {Γ Δ} (w : 𝒲 Δ Γ)
               → ∀ {x y : Setoid.Carrier (𝓡₀.₀ A Γ)}
               → Setoid._≈_ (𝓡₀.₀ A Γ) x y
               → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↑₀-η A Δ (𝓡₀.₁ A w ⟨$⟩ x)) (Repr.+ w (↑₀-η A Γ y))
  ↓₀-commute : ∀ A {Γ Δ} (w : 𝒲 Δ Γ)
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

𝔮 : ∀ Δ → 𝓡 Δ Psh.⇒ Functor.₀ Tm Δ
𝔮 Δ = 𝔦 Δ Psh.∘ ↑ Δ

yoga₀ : ∀ {A} → 𝔦₀ A Psh.∘ ↑₀ A Psh.∘ ↓₀ A Psh.≈ 𝔦₀′ A
yoga₀ {A = ` A `} PE.refl = S.S.refl
yoga₀ {A = A ⇒ B} {Γ} {x} {_} PE.refl =
  S.S.trans
    (S.∷-congᵣ (S.Λ-cong I))
    (S.S.sym (ContextualCartesianClosed.η S.CCC (𝔦₀′-η (A ⇒ B) Γ x)))
  where open Reasoning S.C.setoid

        I = begin
            S.𝒵 (𝔦₀-η B (Γ · A) (↑₀-η B (Γ · A) (↓₀-η B (Γ · A) (Repr.+′ (ω₁ (𝕎.id)) x ⦅ ↑₀-η A (Γ · A) (↓₀-η A (Γ · A) (𝓋 𝓏)) ⦆))))
          ≈⟨ S.𝒵-cong (yoga₀ PE.refl) ⟩
            S.𝒵 (𝔦₀′-η B (Γ · A) (Repr.+′ (ω₁ (𝕎.id)) x ⦅ ↑₀-η A (Γ · A) (↓₀-η A (Γ · A) (𝓋 𝓏)) ⦆))
          ≈⟨ S.app-congᵣ (S.𝒵-cong (yoga₀ PE.refl)) ⟩
            S.𝒵 (𝔦₀′-η (A ⇒ B) (Γ · A) (Repr.+′ (ω₁ 𝕎.id) x)) S.⦅ S.𝓏 ⦆
          ≈⟨ S.app-congₗ (S.𝒵-cong (NaturalTransformation.commute (𝔦₀′ (A ⇒ B)) (ω₁ (𝕎.id {Γ})) {x = x} PE.refl)) ⟩
            S.𝓏 S.[ 𝔦₀′-η (A ⇒ B) Γ x S.∘ (W.₁ (𝕎.id {Γ}) S.∘ S.π S.id) ] S.⦅ S.𝓏 ⦆
          ≈⟨ S.app-congₗ (S.sb-congᵣ (S.∘-congᵣ (S.∘-congₗ (W.identity {Γ})))) ⟩
            S.𝓏 S.[ 𝔦₀′-η (A ⇒ B) Γ x S.∘ (S.id S.∘ S.π S.id) ] S.⦅ S.𝓏 ⦆
          ≈⟨ S.app-congₗ (S.sb-congᵣ (S.∘-congᵣ S.∘-identityˡ)) ⟩
            S.𝓏 S.[ 𝔦₀′-η (A ⇒ B) Γ x S.∘ S.π S.id ] S.⦅ S.𝓏 ⦆
          ≈⟨ S.C.sym (S.app-cong₂ S.vp S.v𝓏) ⟩
            (S.p S.𝓏 S.[ _ S.∷ S.𝓏 ]) S.⦅ S.𝓏 S.[ _ S.∷ S.𝓏 ] ⦆
          ≈⟨ S.C.sym S.sb-app ⟩
            (S.p S.𝓏 S.⦅ S.𝓏 ⦆) S.[ _ S.∷ S.𝓏 ]
          ∎

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↑ Δ Psh.∘ ↓ Δ Psh.≈ 𝔦′ Δ
yoga {Δ = 𝟙}     Repr.!       = S.!η
yoga {Δ = Δ · A} (γ Repr.∷ a) = S.∷-cong₂ (yoga γ) (S.𝒵-cong (yoga₀ a))

⊤′ : Gl.Obj
⊤′ = record
  { α = 𝓡 𝟙
  ; β = 𝟙
  ; f = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = λ _ → S.!
      ; cong = λ _ → S.!η
      }
    ; commute = λ _ _ → S.!η
    })
  }

infixl 6 _·′_

_·′_ : Gl.Obj → 𝒰ᵀ → Gl.Obj
Γ ·′ A = record
  { α = CommaObj.α Γ Psh.·′ 𝓡₀ A
  ; β = CommaObj.β Γ · A
  ; f = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = λ x →
        (NaturalTransformation.η (CommaObj.f Γ) X ⟨$⟩ proj₁ x)
          S.∷ S.𝒵 (NaturalTransformation.η (𝔮 (𝟙 · A)) X ⟨$⟩ (tt , proj₂ x))
      ; cong = λ x≈y →
        S.∷-cong₂ (cong (NaturalTransformation.η (CommaObj.f Γ) X) (proj₁ x≈y))
                  (S.𝒵-cong (cong (NaturalTransformation.η (𝔮 (𝟙 · A)) X) (tt , proj₂ x≈y)))
      }
    ; commute = λ f → λ { {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.∷-cong₂ (S.S.trans (S.S.trans (NaturalTransformation.commute (CommaObj.f Γ) f γ₁≈γ₂) S.∘-identityˡ ) (S.S.sym S.πβ′))
        (S.C.trans (S.C.trans (S.𝒵-cong (NaturalTransformation.commute (𝔮 (𝟙 · A)) f (tt , a₁≈a₂))) S.v𝓏) (S.C.sym S.v𝓏)) }
    })
  }

CC : ContextualCartesian Gl 𝒰ᵀ
CC = record
  { terminal = record
    { ⊤ = ⊤′
    ; ⊤-is-terminal = record
      { ! = record
        { g = Psh.!
        ; h = S.!
        ; commute = λ _ → S.!η
        }
      ; !-unique = λ f → Psh.!-unique (Comma⇒.g f) , S.S.sym S.!η
      }
    }
  ; _·_ = _·′_
  ; π = λ {Δ} → record
    { g = Psh.π
    ; h = S.π S.id
    ; commute = λ { {Γ} {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.S.trans S.πβ′ (cong (NaturalTransformation.η (CommaObj.f Δ) Γ) γ₁≈γ₂) }
    }
  ; 𝓏 = λ {_} {A} → record
    { g = Psh.𝓏
    ; h = S.! S.∷ S.𝓏
    ; commute = λ { {Γ} {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.∷-congᵣ (S.C.trans S.v𝓏 (S.𝒵-cong (cong (NaturalTransformation.η (𝔮 (𝟙 · A)) Γ) (tt , a₁≈a₂)))) }
    }
  ; extensions = λ {Γ} {A} → record
    { ⟨_,_⟩ = λ {Δ} γ a → record
      { g = Psh.⟨ Comma⇒.g γ , Comma⇒.g a ⟩
      ; h = Comma⇒.h γ S.∷ S.𝒵 (Comma⇒.h a)
      ; commute = λ {Γ′} {δ} {δ′} δ≈δ′ →
        S.∷-cong₂ (Comma⇒.commute γ δ≈δ′)
                  (S.C.trans (S.sb-comp {γ = Comma⇒.h a}) (S.𝒵-cong (Comma⇒.commute a δ≈δ′)))
      }
    ; project₁ = λ {Γ} {h} {i} →
      ( (λ {Δ} x → cong (NaturalTransformation.η (Comma⇒.g h) Δ) x)
      , S.πβ′
      )
    ; project₂ = λ {Γ} {h} {i} →
      ( (λ {Δ} x → tt , proj₂ (cong (NaturalTransformation.η (Comma⇒.g i) Δ) x))
      , S.S.trans (S.∷-congᵣ S.v𝓏) S.𝒵η
      )
    ; unique = λ {Δ} {h} {i} {j} x y →
      ( ContextualCartesian.Ext.unique (Psh.CC λ A₀ → 𝔑𝔣₀ ` A₀ `)
          {CommaObj.α Γ} {A} {h = Comma⇒.g h} {Comma⇒.g i} {Comma⇒.g j} (proj₁ x) (proj₁ y)
      , ContextualCartesian.Ext.unique S.CC (proj₂ x) (S.S.trans (proj₂ y) (S.S.sym S.𝒵η))
      )
    }
  }

CCC : ContextualCartesianClosed Gl 𝒰
CCC = record
  { cartesian = CC
  ; Λ = λ f → record
    { g = Psh.Λ (Comma⇒.g f)
    ; h = S.! S.∷ S.Λ (S.𝒵 (Comma⇒.h f))
    ; commute = λ x → {!!}
    }
  ; eval = λ {A} {B} → record
    { g = Psh.eval
    ; h = ContextualCartesianClosed.eval S.CCC
    ; commute = λ {Γ} {x₁} {x₂} x₁≈x₂ → eval-commute {A} {B} {Γ} {x₁} {x₂} x₁≈x₂
    }
  ; β = λ {Γ} {A} {B} f →
    ( ContextualCartesianClosed.β (Psh.CCC λ A₀ → 𝔑𝔣₀ ` A₀ `) {CommaObj.α Γ} {A} {B} (Comma⇒.g f)
    , ContextualCartesianClosed.β S.CCC (Comma⇒.h f)
    )
  ; unique = λ {Γ} {A} {B} {g} {h} x →
    ( ContextualCartesianClosed.unique (Psh.CCC λ A₀ → 𝔑𝔣₀ ` A₀ `)
        {CommaObj.α Γ} {A} {B} {Comma⇒.g g} {Comma⇒.g h} (proj₁ x)
    , ContextualCartesianClosed.unique S.CCC (proj₂ x)
    )
  }
  where eval-commute : ∀ {A B Γ x₁ x₂} → Setoid._≈_ (Functor.₀ (CommaObj.α (⊤′ ·′ A ⇒ B ·′ A)) Γ) x₁ x₂ → _
        eval-commute {A} {B} {Γ} {(_ , f₁) , x₁} {(_ , f₂) , x₂} ((_ , f₁≈f₂) , x₁≈x₂) = S.∷-congᵣ (begin
            (S.p S.𝓏 S.⦅ S.𝓏 ⦆) S.[ α.η Γ ⟨$⟩ ((_ , f₁) , x₁) ]
          ≈⟨ S.sb-app ⟩
            (S.p S.𝓏  S.[ α.η Γ ⟨$⟩ ((_ , f₁) , x₁) ]) S.⦅ S.𝓏 S.[ α.η Γ ⟨$⟩ ((_ , f₁) , x₁) ] ⦆
          ≈⟨ S.app-cong₂ (S.C.trans S.vp S.v𝓏) S.v𝓏 ⟩
            (S.Λ (S.𝒵 (𝔮B.η (Γ · A) ⟨$⟩ (f₁.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))) S.⦅ S.𝒵 (𝔮A.η Γ ⟨$⟩ (tt , x₁)) ⦆)
          ≈⟨ S.Λβ ⟩
            S.𝒵 (𝔮B.η (Γ · A) ⟨$⟩ (f₁.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id))) S.[ S.id S.∷ S.𝒵 (𝔮A.η Γ ⟨$⟩ (tt , x₁)) ]
          ≈⟨ {!!} ⟩
            S.𝒵 (𝔮B.η Γ ⟨$⟩ (f₂.η Γ ⟨$⟩ (x₂ , 𝕎.id)))
          ∎)
          where open Reasoning S.C.setoid
                module 𝔮A = NaturalTransformation (𝔮 (𝟙 · A))
                module 𝔮B = NaturalTransformation (𝔮 (𝟙 · B))
                module f₁ = NaturalTransformation f₁
                module f₂ = NaturalTransformation f₂
                module α = NaturalTransformation (CommaObj.f (⊤′ ·′ A ⇒ B ·′ A))
