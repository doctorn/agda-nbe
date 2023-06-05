{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Category.Instance.Presheaves
  {ℓ}
  (𝒞 : Category ℓ ℓ ℓ)
  where

open import Function.Equality using (_⟨$⟩_; cong)

open import Relation.Binary using (Setoid)

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Yoneda
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Presheaves using (Presheaves)

import TDPE.Gluing.Categories.Category.Instance.Setoids {ℓ} as Setoids

open Category (Presheaves {o′ = ℓ} {ℓ′ = ℓ} 𝒞)

⊤′ : Obj
⊤′ = record
  { F₀ = λ _ → Setoids.⊤′
  ; F₁ = λ _ → Category.id (Setoids ℓ ℓ)
  ; identity = λ _ → tt
  ; homomorphism = λ _ → tt
  ; F-resp-≈ = λ _ _ → tt
  }

! : ∀ {X} → X ⇒ ⊤′
! = record
  { η = λ _ → Setoids.!
  ; commute = λ _ _ → tt
  ; sym-commute = λ _ _ → tt
  }

!-unique : ∀ {X} (h : X ⇒ ⊤′) → h ≈ !
!-unique _ _ = tt

infixl 6 _·′_

_·′_ : Obj → Obj → Obj
Γ ·′ A = record
 { F₀ = λ c → Γ.₀ c Setoids.·′ A.₀ c
 ; F₁ = λ f → record
   { _⟨$⟩_ = λ x → Γ.₁ f ⟨$⟩ proj₁ x , A.₁ f ⟨$⟩ proj₂ x
   ; cong = λ x≈y → cong (Γ.₁ f) (proj₁ x≈y) , cong (A.₁ f) (proj₂ x≈y)
   }
 ; identity = λ x → Γ.identity (proj₁ x) , A.identity (proj₂ x)
 ; homomorphism = λ x → (Γ.homomorphism (proj₁ x)) , (A.homomorphism (proj₂ x))
 ; F-resp-≈ = λ f≈g x → (Γ.F-resp-≈ f≈g (proj₁ x)) , (A.F-resp-≈ f≈g (proj₂ x))
 }
 where module Γ = Functor Γ
       module A = Functor A

⟨_,_⟩ : ∀ {Γ A} {Δ} → Δ ⇒ Γ → Δ ⇒ ⊤′ ·′ A → Δ ⇒ Γ ·′ A
⟨ γ , a ⟩ = record
  { η = λ c → Setoids.⟨ γ.η c , a.η c ⟩
  ; commute = λ f → {!!}
  ; sym-commute = {!!}
  }
  where module γ = NaturalTransformation γ
        module a = NaturalTransformation a

π : ∀ {Γ A} → Γ ·′ A ⇒ Γ
π = record
  { η = λ c → Setoids.π
  ; commute = {!!}
  ; sym-commute = {!!}
  }

𝓏 : ∀ {Γ A} → Γ ·′ A ⇒ ⊤′ ·′ A
𝓏 = record
  { η = λ c → Setoids.𝓏
  ; commute = {!!}
  ; sym-commute = {!!}
  }

module Y = Functor (Yoneda.embed 𝒞)

_^′_ : Obj → Obj → Obj
P ^′ Q = record
  { F₀ = λ c → hom-setoid {A = P ·′ Y.₀ c} {B = Q}
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ x → record
      { η = {!!}
      ; commute = {!!}
      ; sym-commute = {!!}
      }
    ; cong = {!!}
    }
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≈ = {!!}
  }

module _ {a} (𝒰 : Set a) (∣_∣ : 𝒰 → Obj) where

  open import TDPE.Gluing.Contexts 𝒰 renaming (_⇒_ to _^_)

  ∥_∥ : 𝒰ᵀ → Obj
  ∥ ` A ` ∥ = ∣ A ∣
  ∥ A ^ B ∥ = record
    { F₀ = {!!}
    ; F₁ = {!!}
    ; identity = {!!}
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!}
    }
