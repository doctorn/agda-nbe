{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module TDPE.Gluing.Categories.Category.Instance.Presheaves
  {ℓ}
  (𝒞 : Category ℓ ℓ ℓ)
  where

open import Function.Equality using (_⟨$⟩_; cong)

open import Relation.Binary using (Setoid; IsEquivalence)

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Yoneda
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Presheaves using (Presheaves)

Psh = Presheaves {o′ = ℓ} {ℓ′ = ℓ} 𝒞

import TDPE.Gluing.Categories.Category.Instance.Setoids {ℓ} as S
open import TDPE.Gluing.Categories.Category.ContextualCartesian (Psh)
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed (Psh)

open Category Psh
module 𝒞 = Category 𝒞

⊤′ : Obj
⊤′ = record
  { F₀ = λ _ → S.⊤′
  ; F₁ = λ _ → Category.id (Setoids ℓ ℓ)
  ; identity = λ _ → tt
  ; homomorphism = λ _ → tt
  ; F-resp-≈ = λ _ _ → tt
  }

! : ∀ {X} → X ⇒ ⊤′
! = record
  { η = λ _ → S.!
  ; commute = λ _ _ → tt
  ; sym-commute = λ _ _ → tt
  }

!-unique : ∀ {X} (h : X ⇒ ⊤′) → h ≈ !
!-unique _ _ = tt

infixl 6 _·′_

_·′_ : Obj → Obj → Obj
Γ ·′ A = record
 { F₀ = λ c → Γ.₀ c S.·′ A.₀ c
 ; F₁ = λ f → S.⟨ Γ.₁ f S.∘ S.π , S.fmap (A.₁ f) S.∘ S.𝓏 ⟩
 ; identity = λ x → Γ.identity (proj₁ x) , A.identity (proj₂ x)
 ; homomorphism = λ x → (Γ.homomorphism (proj₁ x)) , (A.homomorphism (proj₂ x))
 ; F-resp-≈ = λ f≈g x → (Γ.F-resp-≈ f≈g (proj₁ x)) , (A.F-resp-≈ f≈g (proj₂ x))
 }
 where module Γ = Functor Γ
       module A = Functor A

↑ : ∀ {A} → A ⇒ ⊤′ ·′ A
↑ {A} = record
  { η = λ X → S.↑
  ; commute = λ f x → tt , cong (A.₁ f) x
  ; sym-commute = λ f x → tt , cong (A.₁ f) x
  }
  where module A = Functor A

↓ : ∀ {A} → ⊤′ ·′ A ⇒ A
↓ {A} = record
  { η = λ X → S.↓
  ; commute = λ f x → cong (A.₁ f) (proj₂ x)
  ; sym-commute = λ f x → cong (A.₁ f) (proj₂ x)
  }
  where module A = Functor A

fmap : ∀ {A B} → A ⇒ B → ⊤′ ·′ A ⇒ ⊤′ ·′ B
fmap f = ↑ ∘ f ∘ ↓

⟨_,_⟩ : ∀ {Γ A} {Δ} → Δ ⇒ Γ → Δ ⇒ ⊤′ ·′ A → Δ ⇒ Γ ·′ A
⟨ γ , a ⟩ = record
  { η = λ c → S.⟨ γ.η c , a.η c ⟩
  ; commute = λ f x → γ.commute f x , proj₂ (a.commute f x)
  ; sym-commute = λ f x → γ.sym-commute f x , proj₂ (a.sym-commute f x)
  }
  where module γ = NaturalTransformation γ
        module a = NaturalTransformation a

π : ∀ {Γ A} → Γ ·′ A ⇒ Γ
π {Γ} = record
  { η = λ c → S.π
  ; commute = λ f x → cong (Γ.₁ f) (proj₁ x)
  ; sym-commute = λ f x → cong (Γ.₁ f) (proj₁ x)
  }
  where module Γ = Functor Γ

𝓏 : ∀ {Γ A} → Γ ·′ A ⇒ ⊤′ ·′ A
𝓏 {A = A} = record
  { η = λ c → S.𝓏
  ; commute = λ f x → tt , cong (A.₁ f) (proj₂ x)
  ; sym-commute = λ f x → tt , cong (A.₁ f) (proj₂ x)
  }
  where module A = Functor A

module Y = Functor (Yoneda.embed 𝒞)

_^′_ : Obj → Obj → Obj
P ^′ Q = record
  { F₀ = λ c → hom-setoid {A = P ·′ Y.₀ c} {B = Q}
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ α → α ∘ ⟨ π , fmap (Y.₁ f) ∘ 𝓏 ⟩
    ; cong = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.∘-resp-≈ʳ (proj₂ x≈y))
    }
  ; identity = λ α≈β x≈y → α≈β (proj₁ x≈y , IsEquivalence.trans 𝒞.equiv 𝒞.identityˡ (proj₂ x≈y))
  ; homomorphism = λ α≈β x≈y → α≈β (proj₁ x≈y , IsEquivalence.trans 𝒞.equiv (𝒞.∘-resp-≈ʳ (proj₂ x≈y)) 𝒞.assoc)
  ; F-resp-≈ = λ f≈g α≈β x≈y → α≈β ((proj₁ x≈y) , (𝒞.∘-resp-≈ f≈g (proj₂ x≈y)))
  }

module _ {a} (𝒰 : Set a) (∣_∣ : 𝒰 → Obj) where

  open import TDPE.Gluing.Contexts 𝒰 renaming (_⇒_ to _^_)

  ∥_∥ : 𝒰ᵀ → Obj
  ∥ ` A ` ∥ = ∣ A ∣
  ∥ A ^ B ∥ = ∥ A ∥ ^′ ∥ B ∥

  CC : ContextualCartesian 𝒰ᵀ
  CC = record
    { terminal = record
      { ⊤ = ⊤′
      ; ⊤-is-terminal = record { ! = ! ; !-unique = !-unique }
      }
    ; _·_ = λ Γ A → Γ ·′ ∥ A ∥
    ; π = λ {Γ} {A} → π {Γ} {∥ A ∥}
    ; 𝓏 = λ {Γ} {A} → 𝓏 {Γ} {∥ A ∥}
    ; extensions = record
      { ⟨_,_⟩ = λ {Δ} γ a → ⟨_,_⟩ {Δ = Δ} γ a
      ; project₁ = λ {Δ} {γ} {_} x → cong (NaturalTransformation.η γ _) x
      ; project₂ = λ {Δ} {_} {a} x → tt , proj₂ (cong (NaturalTransformation.η a _) x)
      ; unique = λ {Δ} {h} {γ} {a} x y z → unique {Δ = Δ} {h} {γ} {a} x y z
      }
    }
    where unique : ∀ {Γ A} {Δ} {h : Δ ⇒ Γ ·′ A} {γ : Δ ⇒ Γ} {a : Δ ⇒ ⊤′ ·′ A}
                   → π ∘ h ≈ γ → 𝓏 ∘ h ≈ a → ⟨ γ , a ⟩ ≈ h
          unique {Γ} {A} {Δ} πh≈γ 𝓏h≈a {X} {x} {y} x≈y =
            Γx.sym (πh≈γ (Δx.sym x≈y)) , proj₂ (Ax.sym (𝓏h≈a (Δx.sym x≈y)))
            where module Γx = IsEquivalence (Setoid.isEquivalence (Functor.₀ Γ X))
                  module Ax = IsEquivalence (Setoid.isEquivalence (Functor.₀ (⊤′ ·′ A) X))
                  module Δx = IsEquivalence (Setoid.isEquivalence (Functor.₀ Δ X))
