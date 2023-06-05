{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module TDPE.Gluing.Categories.Category.Instance.Setoids
  {a ℓ} (𝒰 : Set a) (∣_∣ : 𝒰 → Setoid ℓ ℓ) where

open import Level

open import Function.Equality using (_⟨$⟩_; cong)

open import Relation.Binary using (IsEquivalence)

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)

open import Categories.Category.Core
open import Categories.Category.Instance.Setoids public


open import TDPE.Gluing.Categories.Category.ContextualCartesian (Setoids ℓ ℓ)
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed (Setoids ℓ ℓ)
open import TDPE.Gluing.Contexts 𝒰 renaming (_⇒_ to _^_)

open Category (Setoids ℓ ℓ)

⊤′ : Setoid ℓ ℓ
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

_^′_ : Setoid ℓ ℓ → Setoid ℓ ℓ → Setoid ℓ ℓ
A ^′ B = hom-setoid {A} {B}

∥_∥ : 𝒰ᵀ → Setoid ℓ ℓ
∥ ` A ` ∥ = ∣ A ∣
∥ A ^ B ∥ = ∥ A ∥ ^′ ∥ B ∥

infixl 6 _·′_

_·′_ : Setoid ℓ ℓ → Setoid ℓ ℓ → Setoid ℓ ℓ
X ·′ A = ×-setoid X A

⟨_,_⟩ : ∀ {Γ A} {Δ} → Δ ⇒ Γ → Δ ⇒ ⊤′ ·′ A → Δ ⇒ Γ ·′ A
⟨ γ , a ⟩ = record
  { _⟨$⟩_ = λ x → γ ⟨$⟩ x , proj₂ (a ⟨$⟩ x)
  ; cong = λ x → cong γ x , proj₂ (cong a x)
  }

π : ∀ {Γ A} → Γ ·′ A ⇒ Γ
π = record
  { _⟨$⟩_ = proj₁
  ; cong = proj₁
  }

𝓏 : ∀ {Γ A} → Γ ·′ A ⇒ ⊤′ ·′ A
𝓏 = record
  {  _⟨$⟩_ = λ x → tt , proj₂ x
  ; cong = λ x → tt , proj₂ x
  }

Setoids-CC : ContextualCartesian 𝒰ᵀ
Setoids-CC = record
  { terminal = record
    { ⊤ = ⊤′
    ; ⊤-is-terminal = record { ! = ! ; !-unique = !-unique }
    }
  ; _·_ = λ Γ A → Γ ·′ ∥ A ∥
  ; π = λ {Γ} {A} → π {Γ} {∥ A ∥}
  ; 𝓏 = λ {Γ} {A} → 𝓏 {Γ} {∥ A ∥}
  ; extensions = record
    { ⟨_,_⟩ = λ {Δ} γ a → ⟨_,_⟩ {Δ = Δ} γ a
    ; project₁ = λ {_} {γ} x → cong γ x
    ; project₂ = λ {_} {_} {a} x → tt , proj₂ (cong a x)
    ; unique = λ {Δ} {h} {γ} {a} x y z → unique {Δ = Δ} {h} {γ} {a} x y z
    }
  }
  where unique : ∀ {Γ A} {Δ} {h : Δ ⇒ Γ ·′ A} {γ : Δ ⇒ Γ} {a : Δ ⇒ ⊤′ ·′ A}
                 → π ∘ h ≈ γ → 𝓏 ∘ h ≈ a → ⟨ γ , a ⟩ ≈ h
        unique {Γ} {A} {Δ} {h} {γ} {a} πh≈γ 𝓏h≈a x≈y =
          (Γ.sym (πh≈γ (Δ.sym x≈y))) , proj₂ (A.sym (𝓏h≈a (Δ.sym x≈y)))
          where module Γ = IsEquivalence (Setoid.isEquivalence Γ)
                module A = IsEquivalence (Setoid.isEquivalence (⊤′ ·′ A))
                module Δ = IsEquivalence (Setoid.isEquivalence Δ)

Λ : ∀ {Γ A B} → Γ ·′ A ⇒ ⊤′ ·′ B → Γ ⇒ ⊤′ ·′ A ^′ B
Λ {Γ} f = record
  { _⟨$⟩_ = λ γ → tt , record
    { _⟨$⟩_ = λ a → proj₂ (f ⟨$⟩ (γ , a))
    ; cong = λ x → proj₂ (cong f (IsEquivalence.refl (Setoid.isEquivalence Γ)  , x))
    }
  ; cong = λ f≈g → tt , λ a≈b → proj₂ (cong f (f≈g , a≈b))
  }

eval : ∀ {A B} → ⊤′ ·′ (A ^′ B) ·′ A ⇒ ⊤′ ·′ B
eval = record { _⟨$⟩_ = λ γ → tt , proj₂ (proj₁ γ) ⟨$⟩ proj₂ γ
              ; cong = λ γ≈δ → tt , proj₂ (proj₁ γ≈δ) (proj₂ γ≈δ)
              }

β : ∀ {Γ A B} (f : Γ ·′ A ⇒ ⊤′ ·′ B) → eval ∘ ⟨ Λ f ∘ π , 𝓏 ⟩ ≈ f
β {B = B} f (γ≈δ , a≈b) = cong f (γ≈δ , a≈b)

unique : ∀ {Γ A B} {g : Γ ·′ A ⇒ ⊤′ ·′ B} {h : Γ ⇒ ⊤′ ·′ A ^′ B}
         → eval ∘ ⟨ h ∘ π , 𝓏 ⟩ ≈ g
         → h ≈ Λ g
unique {B = B} ϵ⟨hπ,𝓏⟩≈g γ≈δ = tt , λ a≈b → proj₂ (ϵ⟨hπ,𝓏⟩≈g (γ≈δ , a≈b))
  where open IsEquivalence (Setoid.isEquivalence B)

Setoids-CCC : ContextualCartesianClosed 𝒰
Setoids-CCC = record
  { cartesian = Setoids-CC
  ; Λ = λ {Γ} {A} {B} f → Λ {Γ} {∥ A ∥} {∥ B ∥} f
  ; eval = λ {A} {B} → eval {∥ A ∥} {∥ B ∥}
  ; β = λ {Γ} {A} {B} → β {Γ} {∥ A ∥} {∥ B ∥}
  ; unique = λ {Γ} {A} {B} {g} {h} → unique {Γ} {∥ A ∥} {∥ B ∥} {g} {h}
  }
