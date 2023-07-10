{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Cartesian {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Glue.Yoga 𝒰 using (𝓡; 𝓡₀; ↓₀)

open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁; ω₂; 𝒲)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)

⊤ : Gl.Obj
⊤ = record
  { α = 𝓡 𝟙
  ; β = 𝟙
  ; f = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = λ _ → !
      ; cong = λ _ → !η
      }
    ; commute = λ _ _ → !η
    })
  }

infixl 6 _×_

_×_ : Gl.Obj → 𝒰ᵀ → Gl.Obj
Γ × A = record
  { α = CommaObj.α Γ Psh.× 𝓡₀ A
  ; β = CommaObj.β Γ · A
  ; f = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = λ { (γ , a) →
        (NaturalTransformation.η (CommaObj.f Γ) X ⟨$⟩ γ) ∷ 𝒵 (𝔦₀.η A X ⟨$⟩ (↓₀.η A X ⟨$⟩ a)) }
      ; cong = λ { (γ , a) →
        ∷-cong₂ (cong (NaturalTransformation.η (CommaObj.f Γ) X) γ) (𝒵-cong (cong (𝔦₀.η A X) (cong (↓₀.η A X) a))) }
      }
    ; commute = λ f → λ { {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      ∷-cong₂ (S.trans (S.trans (NaturalTransformation.commute (CommaObj.f Γ) f γ₁≈γ₂) ∘-identityˡ) (S.sym πβ′))
        (C.trans
          (𝒵-cong (NaturalTransformation.commute (𝔦₀ A Psh.∘ ↓₀ A) f a₁≈a₂))
          (C.sym (C.trans v𝓏 (C.trans (sb-comp {γ = 𝔦₀.η A _ ⟨$⟩ (↓₀.η A _ ⟨$⟩ a₂)}) (C.sym v𝒵))))) }
    })
  }

CC : ContextualCartesian Gl 𝒰ᵀ
CC = record
  { terminal = record
    { ⊤ = ⊤
    ; ⊤-is-terminal = record
      { ! = record
        { g = Psh.!
        ; h = !
        ; commute = λ _ → !η
        }
      ; !-unique = λ f → Psh.!-unique (Comma⇒.g f) , S.sym !η
      }
    }
  ; _·_ = _×_
  ; π = λ {Δ} → record
    { g = Psh.π
    ; h = π id
    ; commute = λ { {Γ} {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.trans πβ′ (cong (NaturalTransformation.η (CommaObj.f Δ) Γ) γ₁≈γ₂) }
    }
  ; 𝓏 = λ {_} {A} → record
    { g = Psh.unit Psh.∘ Psh.𝓏
    ; h = ! ∷ 𝓏
    ; commute = λ { {Γ} {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      ∷-congᵣ (C.trans v𝓏 (𝒵-cong (cong (NaturalTransformation.η (𝔦₀ A Psh.∘ ↓₀ A) Γ) a₁≈a₂))) }
    }
  ; extensions = λ {Γ} {A} → record
    { ⟨_,_⟩ = λ {Δ} γ a → record
      { g = Psh.⟨ Comma⇒.g γ , Psh.counit Psh.∘ Comma⇒.g a ⟩
      ; h = Comma⇒.h γ ∷ 𝒵 (Comma⇒.h a)
      ; commute = λ {Γ′} {δ} {δ′} δ≈δ′ →
        ∷-cong₂ (Comma⇒.commute γ δ≈δ′)
                (C.trans (sb-comp {γ = Comma⇒.h a}) (𝒵-cong (Comma⇒.commute a δ≈δ′)))
      }
    ; project₁ = λ {Γ} {h} {i} →
      ( (λ {Δ} x → cong (NaturalTransformation.η (Comma⇒.g h) Δ) x)
      , πβ′
      )
    ; project₂ = λ {Γ} {h} {i} →
      ( (λ {Δ} x → tt , proj₂ (cong (NaturalTransformation.η (Comma⇒.g i) Δ) x))
      , S.trans (∷-congᵣ v𝓏) 𝒵η
      )
    ; unique = λ {Δ} {h} {i} {j} x y →
      ( ContextualCartesian.Ext.unique (Psh.CC 𝓡₀)
        {CommaObj.α Γ} {A} {CommaObj.α Δ} {Comma⇒.g h} {Comma⇒.g i} {Comma⇒.g j} (proj₁ x) (proj₁ y)
      , ContextualCartesian.Ext.unique Syntax.CC (proj₂ x) (S.trans (proj₂ y) (S.sym 𝒵η))
      )
    }
  }
