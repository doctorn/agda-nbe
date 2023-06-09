{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)
open import Categories.Category.Construction.Presheaves using (Presheaves)
open import Categories.Yoneda

open import TDPE.Gluing.Categories.Functor.Properties using (precompose)
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ⟦_⟧)
import TDPE.Gluing.Syntax 𝒰 as Syntax

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Relation.Binary using (IsEquivalence; Setoid)

i : Functor 𝕎 Syntax.𝕋𝕞
i = ⟦_⟧ Syntax.CC

Tm : Functor Syntax.𝕋𝕞 (Presheaves 𝕎)
Tm = precompose (Functor.op i) ∘F Yoneda.embed Syntax.𝕋𝕞

Gl : Category (suc a) a a
Gl = Comma {A = Presheaves 𝕎} Categories.Functor.id Tm

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

𝔑𝔣₀ : 𝒰 → Psh.Obj
𝔑𝔣₀ = {!!}

𝓡₀ : 𝒰ᵀ → Psh.Obj
𝓡₀ A = ⟦ A ⟧ᵀ 𝔑𝔣₀ Psh._^′_

𝓡 : ℭ → Psh.Obj
𝓡 Γ = ⟦ Γ ⟧ᶜ 𝔑𝔣₀ Psh._^′_ Psh.⊤′ Psh._·′_

𝔑𝔣 : ℭ → Psh.Obj
𝔑𝔣 = {!!}

𝔑𝔢 : ℭ → Psh.Obj
𝔑𝔢 = {!!}

↓ : ∀ Δ → 𝓡 Δ Psh.⇒ 𝔑𝔣 Δ
↓ = {!!}

↑ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ 𝓡 Δ
↑ = {!!}

𝔦 : ∀ Δ → 𝔑𝔣 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦 = {!!}

𝔦′ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ Functor.₀ Tm Δ
𝔦′ = {!!}

𝔮 : ∀ Δ → 𝓡 Δ Psh.⇒ Functor.₀ Tm Δ
𝔮 Δ = 𝔦 Δ Psh.∘ ↓ Δ

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↓ Δ Psh.∘ ↑ Δ Psh.≈ 𝔦′ Δ
yoga = {!!}

CC : ContextualCartesian Gl 𝒰ᵀ
CC = record
  { terminal = record
    { ⊤ = record
      { α = 𝓡 𝟙
      ; β = 𝟙
      ; f = ntHelper (record
        { η = λ X → record
          { _⟨$⟩_ = λ _ → Syntax.!
          ; cong = λ _ → Syntax.!η
          }
        ; commute = λ _ _ → Syntax.!η
        })
      }
    ; ⊤-is-terminal = record
      { ! = record
        { g = Psh.!
        ; h = Syntax.!
        ; commute = λ _ → Syntax.!η
        }
      ; !-unique = λ f → Psh.!-unique (Comma⇒.g f) , Syntax.S.sym Syntax.!η
      }
    }
  ; _·_ = λ Γ A → record
    { α = CommaObj.α Γ Psh.·′ 𝓡₀ A
    ; β = CommaObj.β Γ · A
    ; f = ntHelper (record
      { η = λ X → record
        { _⟨$⟩_ = λ x →
          (NaturalTransformation.η (CommaObj.f Γ) X ⟨$⟩ proj₁ x)
            Syntax.∷ Syntax.𝒵 (NaturalTransformation.η (𝔮 (𝟙 · A)) X ⟨$⟩ (tt , proj₂ x))
        ; cong = λ x≈y →
          Syntax.∷-cong₂ (cong (NaturalTransformation.η (CommaObj.f Γ) X) (proj₁ x≈y))
                         (Syntax.𝒵-cong (cong (NaturalTransformation.η (𝔮 (𝟙 · A)) X) (tt , proj₂ x≈y)))
        }
      ; commute = λ f x → {!!}
      })
    }
  ; π = record
    { g = Psh.π
    ; h = Syntax.π Syntax.id
    ; commute = {!!}
    }
  ; 𝓏 = record
    { g = Psh.𝓏
    ; h = Syntax.! Syntax.∷ Syntax.𝓏
    ; commute = {!!}
    }
  ; extensions = record
    { ⟨_,_⟩ = λ γ a → record
      { g = Psh.⟨ Comma⇒.g γ , Comma⇒.g a ⟩
      ; h = Comma⇒.h γ Syntax.∷ Syntax.𝒵 (Comma⇒.h a)
      ; commute = {!!}
      }
    ; project₁ = {!!}
    ; project₂ = {!!}
    ; unique = {!!}
    }
  }
