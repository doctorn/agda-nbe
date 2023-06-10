{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Relation.Binary using (IsEquivalence; Setoid)
import Relation.Binary.PropositionalEquality as PE

open import Categories.Category using (Category)
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

-- TODO(@doctorn) probably remove this
∣_⦅_⦆∣ : Psh.Obj → ℭ → Set _
∣ P ⦅ Γ ⦆∣ = Setoid.Carrier (Functor.₀ P Γ)

↑₀-η : ∀ A Δ → ∣ 𝓡₀ A ⦅ Δ ⦆∣ → ∣ 𝔑𝔣₀ A ⦅ Δ ⦆∣
↓₀-η : ∀ A Δ → ∣ 𝔑𝔢₀ A ⦅ Δ ⦆∣ → ∣ 𝓡₀ A ⦅ Δ ⦆∣

↑₀-η ` A `   Δ x = x
↑₀-η (A ⇒ B) Δ x =
  Λ (↑₀-η B (Δ · A) (proj₂ (x.η (Δ · A) ⟨$⟩ (↓₀-η A (Δ · A) (𝓋 𝓏) , ω₁ (Category.id 𝕎)))))
  where module x = NaturalTransformation x

↓₀-η ` A `   Δ x = ι x
↓₀-η (A ⇒ B) Δ x = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ e → tt , ↓₀-η B Γ (Repr.+′ (proj₂ e) x ⦅ ↑₀-η A Γ (proj₁ e) ⦆)
    ; cong = {!!}
    }
  ; commute = {!!}
  })

↑₀ : ∀ A → 𝓡₀ A Psh.⇒ 𝔑𝔣₀ A
↑₀ A = ntHelper (record
  { η = λ Δ → record
    { _⟨$⟩_ = ↑₀-η A Δ
    ; cong = {!!}
    }
  ; commute = {!!}
  })

↓₀ : ∀ A → 𝔑𝔢₀ A Psh.⇒ 𝓡₀ A
↓₀ A = ntHelper (record
  { η = λ Δ → record
    { _⟨$⟩_ = ↓₀-η A Δ
    ; cong = {!!}
    }
  ; commute = {!!}
  })

↑ : ∀ Δ → 𝓡 Δ Psh.⇒ 𝔑𝔣 Δ
↑ = {!!}

↓ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ 𝓡 Δ
↓ = {!!}

𝔦 : ∀ Δ → 𝔑𝔣 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦 = {!!}

𝔦′ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦′ = {!!}

𝔮 : ∀ Δ → 𝓡 Δ Psh.⇒ Functor.₀ Tm Δ
𝔮 Δ = 𝔦 Δ Psh.∘ ↑ Δ

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↑ Δ Psh.∘ ↓ Δ Psh.≈ 𝔦′ Δ
yoga = {!!}

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
