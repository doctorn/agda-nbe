{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module TDPE.Gluing.Categories.Category.Instance.Setoids {ℓ} where

open import Level

open import Function.Equality using (_⟨$⟩_; cong)

open import Relation.Binary using (IsEquivalence)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Product.Relation.Binary.Pointwise.Dependent
  using (_,_; proj₁; proj₂) renaming (setoid to Σ-setoid)


open import Categories.Category.Core
open import Categories.Category.Instance.Setoids public
open import Categories.Diagram.Pullback (Setoids ℓ ℓ) using (Pullback)

open import TDPE.Gluing.Categories.Category.ContextualCartesian (Setoids ℓ ℓ)
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed (Setoids ℓ ℓ)

open Category (Setoids ℓ ℓ) public

⊤ : Setoid ℓ ℓ
⊤ = record
  { Carrier = Unit.⊤
  ; _≈_ = λ _ _ → Unit.⊤
  ; isEquivalence = record
    { refl = tt
    ; sym = λ _ → tt
    ; trans = λ _ _ → tt
    }
  }

! : ∀ {X} → X ⇒ ⊤
! = record { _⟨$⟩_ = λ _ → tt ; cong = λ _ → tt }

!-unique : ∀ {X} (h : X ⇒ ⊤) → h ≈ !
!-unique _ _ = tt

infixl 6 _×_

_×_ : Obj → Obj → Obj
Γ × A = ×-setoid Γ A

_⊗_ : ∀ {A B C} (f : A ⇒ C) (g : B ⇒ C) → Pullback f g
_⊗_ {A} {B} {C} f g = record
  { P = Σ-setoid (A × B) (record
    { Carrier = λ { (a , b) → f ⟨$⟩ a C.≈ g ⟨$⟩ b }
    ; _≈_ = λ _ _ → Unit.⊤ {ℓ}
    ; isEquivalence = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    })
  ; p₁ = record { _⟨$⟩_ = λ { ((a , _) , _) → a } ; cong = λ x → proj₁ (proj₁ x) }
  ; p₂ = record { _⟨$⟩_ = λ { ((_ , b) , _) → b } ; cong = λ x → proj₂ (proj₁ x) }
  ; isPullback = record
    { commute = λ { {(a₁ , b₁) , p} {(a₂ , b₂) , _} ((a₁≈a₂ , b₁≈b₂) , _) → C.trans p (cong g b₁≈b₂) }
    ; universal = λ {H} {h₁} {h₂} p → record
      { _⟨$⟩_ = λ x → (h₁ ⟨$⟩ x , h₂ ⟨$⟩ x) , p (Setoid.refl H)
      ; cong = λ x → (cong h₁ x , cong h₂ x) , tt
      }
    ; unique = λ {H} {h₁} {h₂} {i} {fh₁≈gh₂} p₁i≈h₁ p₂i≈h₂ p → (p₁i≈h₁ p , p₂i≈h₂ p) , tt
    ; p₁∘universal≈h₁ = λ {_} {h₁} x → cong h₁ x
    ; p₂∘universal≈h₂ = λ {_} {_} {h₂} x → cong h₂ x
    }
  }
  where module C = Setoid C

unit : ∀ {A} → A ⇒ ⊤ × A
unit = record { _⟨$⟩_ = tt ,_ ; cong = tt ,_ }

counit : ∀ {A} → ⊤ × A ⇒ A
counit = record { _⟨$⟩_ = proj₂ ; cong = proj₂ }

fmap : ∀ {A B} → A ⇒ B → ⊤ × A ⇒ ⊤ × B
fmap f = unit ∘ f ∘ counit

⟨_,_⟩ : ∀ {Γ A} {Δ} → Δ ⇒ Γ → Δ ⇒ A → Δ ⇒ Γ × A
⟨ γ , a ⟩ = record
  { _⟨$⟩_ = λ x → γ ⟨$⟩ x , a ⟨$⟩ x
  ; cong = λ x → cong γ x , cong a x
  }

π : ∀ {Γ A} → Γ × A ⇒ Γ
π = record
  { _⟨$⟩_ = proj₁
  ; cong = proj₁
  }

𝓏 : ∀ {Γ A} → Γ × A ⇒ A
𝓏 = record
  {  _⟨$⟩_ = λ x → proj₂ x
  ; cong = λ x → proj₂ x
  }

_^_ : Obj → Obj → Obj
A ^ B = hom-setoid {A} {B}

Λ : ∀ {Γ A B} → Γ × A ⇒ B → Γ ⇒ A ^ B
Λ {Γ} f = record
  { _⟨$⟩_ = λ γ → record
    { _⟨$⟩_ = λ a → f ⟨$⟩ (γ , a)
    ; cong = λ x → cong f (Setoid.refl Γ  , x)
    }
  ; cong = λ f≈g → λ a≈b → cong f (f≈g , a≈b)
  }

eval : ∀ {A B} → (A ^ B) × A ⇒ B
eval = record
  { _⟨$⟩_ = λ γ → (proj₁ γ) ⟨$⟩ proj₂ γ
  ; cong = λ γ≈δ → (proj₁ γ≈δ) (proj₂ γ≈δ)
  }

module _ {a} {𝒰 : Set a} (ι : 𝒰 → Obj) where

  open import TDPE.Gluing.Contexts 𝒰 hiding (_⇒_)

  private
    ⟦_⟧ : 𝒰ᵀ → Obj
    ⟦ A ⟧ = ⟦ A ⟧ᵀ ι _^_

  CC : ContextualCartesian 𝒰ᵀ
  CC = record
    { terminal = record
      { ⊤ = ⊤
      ; ⊤-is-terminal = record { ! = ! ; !-unique = !-unique }
      }
    ; _·_ = λ Γ A → Γ × (⟦ A ⟧)
    ; π = λ {Γ} {A} → π {Γ} {⟦ A ⟧}
    ; 𝓏 = λ {Γ} {A} → unit ∘ 𝓏 {Γ} {⟦ A ⟧}
    ; extensions = record
      { ⟨_,_⟩ = λ {Δ} γ a → ⟨_,_⟩ {Δ = Δ} γ (counit ∘ a)
      ; project₁ = λ {_} {γ} x → cong γ x
      ; project₂ = λ {_} {_} {a} x → tt , proj₂ (cong a x)
      ; unique = λ {Δ} {h} {γ} {a} x y z → unique {Δ = Δ} {h} {γ} {a} x y z
      }
    }
    where unique : ∀ {Γ A} {Δ} {h : Δ ⇒ Γ × A} {γ : Δ ⇒ Γ} {a : Δ ⇒ ⊤ × A}
                   → π ∘ h ≈ γ → unit ∘ 𝓏 ∘ h ≈ a → ⟨ γ , counit ∘ a ⟩ ≈ h
          unique {Γ} {A} {Δ} {h} {γ} {a} πh≈γ 𝓏h≈a x≈y =
            (Γ.sym (πh≈γ (Δ.sym x≈y))) , proj₂ (A.sym (𝓏h≈a (Δ.sym x≈y)))
            where module Γ = Setoid Γ
                  module A = Setoid (⊤ × A)
                  module Δ = Setoid Δ

  CCC : ContextualCartesianClosed 𝒰
  CCC = record
    { cartesian = CC
    ; Λ = λ {Γ} {A} {B} f → Λ′ {Γ} {⟦ A ⟧} {⟦ B ⟧} f
    ; eval = λ {A} {B} → eval′ {⟦ A ⟧} {⟦ B ⟧}
    ; β = λ f x → cong f x
    ; unique = λ x y → tt , λ z → proj₂ (x (y , z))
    }
    where Λ′ : ∀ {Γ A B} → Γ × A ⇒ ⊤ × B → Γ ⇒ ⊤ × A ^ B
          Λ′ f = unit ∘ Λ (counit ∘ f)

          eval′ : ∀ {A B} → ⊤ × (A ^ B) × A ⇒ ⊤ × B
          eval′ = unit ∘ eval ∘ ⟨ 𝓏 ∘ π , 𝓏 ⟩
