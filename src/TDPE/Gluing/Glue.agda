{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Relation.Binary using (IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as Reasoning
import Relation.Binary.PropositionalEquality as PE

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

          I : w 𝕎.∘ 𝕎.id PE.≡ 𝕎.id 𝕎.∘ (𝕎.id 𝕎.∘ w)
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

{-
𝔦 : ∀ Δ → 𝔑𝔣 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦 = {!!}

𝔦′ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦′ = {!!}

𝔮 : ∀ Δ → 𝓡 Δ Psh.⇒ Functor.₀ Tm Δ
𝔮 Δ = 𝔦 Δ Psh.∘ ↑ Δ

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↑ Δ Psh.∘ ↓ Δ Psh.≈ 𝔦′ Δ
yoga = {!!}

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
