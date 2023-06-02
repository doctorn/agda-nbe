{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module TDPE.Gluing.Categories.Category.Instance.Setoids
  {a} (𝒰 : Set a) (∣_∣ : 𝒰 → Setoid a a)
  where

open import Level

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)

open import Categories.Category.Core
open import Categories.Category.Instance.Setoids public

open import TDPE.Gluing.Categories.Category.ContextualCartesian (Setoids a a)

open Category (Setoids a a)

⊤′ : ∀ {a ℓ} → Setoid a ℓ
⊤′ = record
  { Carrier = ⊤
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record
    { refl = tt
    ; sym = λ _ → tt
    ; trans = λ _ _ → tt
    }
  }

! : ∀ {X} → X ⇒ ⊤′
! = record { _⟨$⟩_ = λ _ → tt ; cong = λ _ → tt }

!-unique : ∀ {X} (h : X ⇒ ⊤′) → h ≈ !
!-unique _ _ = tt

𝒰+ = Lift (suc a) 𝒰

_·_ : Setoid a a → 𝒰+ → Setoid a a
X · lift A = ×-setoid X ∣ A ∣

Setoids-CC : ContextualCartesian 𝒰+
Setoids-CC = record
  { terminal = record
    { ⊤ = ⊤′
    ; ⊤-is-terminal = record { ! = ! ; !-unique = !-unique }
    }
  ; _·_ = _·_
  ; π = record
    { _⟨$⟩_ = proj₁
    ; cong = proj₁
    }
  ; 𝓏 = record
    { _⟨$⟩_ = λ x → tt , proj₂ x
    ; cong = λ x → tt , proj₂ x
    }
  ; extensions = record
    { ⟨_,_⟩ = {!!}
    ; project₁ = {!!}
    ; project₂ = {!!}
    ; unique = {!!}
    }
  }
