{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue {a} (𝒰 : Set a) where

open import Level
open import Function.Equality

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Construction.Functors
open import Categories.Yoneda

open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ⟦_⟧)
import TDPE.Gluing.Syntax 𝒰 as Syntax

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic

open import Relation.Binary using (IsEquivalence; Setoid)

module _ {o₁ ℓ₁ e₁ o₂ ℓ₂ e₂ o₃ ℓ₃ e₃}
  {A : Category o₁ ℓ₁ e₁}
  {B : Category o₂ ℓ₂ e₂}
  {C : Category o₃ ℓ₃ e₃}
  (F : Functor A B)
  where

  precompose : Functor (Functors B C) (Functors A C)
  precompose = record
                 { F₀ = λ G → G ∘F F
                 ; F₁ = λ α → α ∘ʳ F
                 ; identity = {!!}
                 ; homomorphism = {!!}
                 ; F-resp-≈ = {!!}
                 }

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

𝓡 : 𝒰 → Psh.Obj
𝓡 = {!!}

CC : ContextualCartesian Gl 𝒰ᵀ
CC = record
  { terminal = record
    { ⊤ = record
      { α = Psh.⊤′
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
    { α = CommaObj.α Γ Psh.·′ Psh.∥_∥ 𝒰 𝓡 A
    ; β = CommaObj.β Γ · A
    ; f = ntHelper (record
      { η = λ X → record
        { _⟨$⟩_ = {!!} -- λ x → (NaturalTransformation.η Psh.π X ⟨$⟩ x)
          -- Syntax.∷ proj₂ (NaturalTransformation.η Psh.𝓏 X ⟨$⟩ x)
        ; cong = {!!} -- λ x → Syntax.∷-cong₂ (cong (NaturalTransformation.η Psh.π X) x)
          -- (proj₂ (cong (NaturalTransformation.η Psh.𝓏 X) x))
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
