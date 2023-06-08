{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module TDPE.Gluing.Categories.Category.Instance.Presheaves
  {ℓ}
  (𝒞 : Category ℓ ℓ ℓ)
  where

open import Function.Equality using (_⟨$⟩_; cong)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Yoneda
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Presheaves using (Presheaves)

Psh = Presheaves {o′ = ℓ} {ℓ′ = ℓ} 𝒞

import TDPE.Gluing.Categories.Category.Instance.Setoids {ℓ} as S
open import TDPE.Gluing.Categories.Category.ContextualCartesian (Psh)
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed (Psh)

open Category Psh public
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

module 𝕪 = Functor (Yoneda.embed 𝒞)

Env : Obj → 𝒞.Obj → Obj
Env P X = P ·′ 𝕪.₀ X

_^′_ : Obj → Obj → Obj
P ^′ Q = record
  { F₀ = λ X → hom-setoid {A = Env P X} {B = ⊤′ ·′ Q}
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ α → α ∘ ⟨ π , fmap (𝕪.₁ f) ∘ 𝓏 ⟩
    ; cong = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.∘-resp-≈ʳ (proj₂ x≈y))
    }
  ; identity = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.Equiv.trans 𝒞.identityˡ (proj₂ x≈y))
  ; homomorphism = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.Equiv.trans (𝒞.∘-resp-≈ʳ (proj₂ x≈y)) 𝒞.assoc)
  ; F-resp-≈ = λ f≈g α≈β x≈y → α≈β ((proj₁ x≈y) , (𝒞.∘-resp-≈ f≈g (proj₂ x≈y)))
  }

Λ : ∀ {Γ A B} → Γ ·′ A ⇒ ⊤′ ·′ B → Γ ⇒ ⊤′ ·′ A ^′ B
Λ {Γ} {A} {B} f = ↑ ∘ (ntHelper (record
  { η = Λ₀′
  ; commute = commute
  }))
  where module Γ = Functor Γ
        module A = Functor A
        module B = Functor (⊤′ ·′ B)
        module Γ·A = Functor (Γ ·′ A)
        module A^B = Functor (A ^′ B)
        module f = NaturalTransformation f

        e : ∀ X → Setoid.Carrier (Γ.₀ X)
            → ∀ Y → Setoid.Carrier (Functor.₀ (Env A X) Y) → Setoid.Carrier (B.₀ Y)
        e X θ Y (a , h) = f.η Y ⟨$⟩ (Γ.₁ h ⟨$⟩ θ , a)

        e′ : ∀ X → Setoid.Carrier (Γ.₀ X)
             → ∀ Y → (Functor.₀ (Env A X) Y) S.⇒ B.₀ Y
        e′ X θ Y = record
          { _⟨$⟩_ = e X θ Y
          ; cong = λ x → cong (f.η Y) (Γ.F-resp-≈ (proj₂ x) refl , proj₁ x)
          }
          where open IsEquivalence (Setoid.isEquivalence (Γ.₀ X))

        Λ₀ : ∀ X → Setoid.Carrier (Γ.₀ X) → Setoid.Carrier (A^B.₀ X)
        Λ₀ X θ = ntHelper (record
          { η = λ Y → e′ X θ Y
          ; commute = commute
          })
          where commute : ∀ {Y Z} (g : Y 𝒞.⇒ Z)
                          → e′ X θ Y S.∘ Functor.₁ (Env A X) g S.≈ B.₁ g S.∘ e′ X θ Z
                commute {Y} {Z} g {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = begin
                    f.η Y ⟨$⟩ (Γ.₁ (Functor.₁ (𝕪.₀ X) g ⟨$⟩ y₁) ⟨$⟩ θ , A.₁ g ⟨$⟩ x₁)
                  ≈⟨ cong (f.η Y) (Γ.F-resp-≈ 𝒞.identityˡ ΓEquiv.refl , AEquiv.refl) ⟩
                    f.η Y ⟨$⟩ (Γ.₁ (y₁ 𝒞.∘ g) ⟨$⟩ θ , A.₁ g ⟨$⟩ x₁)
                  ≈⟨ cong (f.η Y) (Γ.homomorphism ΓEquiv.refl , AEquiv.refl) ⟩
                    f.η Y ⟨$⟩ (Γ·A.₁ g ⟨$⟩ (Γ.₁ y₁ ⟨$⟩ θ , x₁))
                  ≈⟨ f.commute g (Γ.F-resp-≈ y₁≈y₂ ΓEquiv.refl , x₁≈x₂) ⟩
                    B.₁ g ⟨$⟩ (f.η Z ⟨$⟩ (Γ.₁ y₂ ⟨$⟩ θ , x₂))
                  ∎
                  where open Reasoning (B.₀ Y)
                        module ΓEquiv = IsEquivalence (Setoid.isEquivalence (Γ.₀ X))
                        module AEquiv = IsEquivalence (Setoid.isEquivalence (A.₀ Y))

        Λ₀′ : ∀ X → Γ.₀ X S.⇒ A^B.₀ X
        Λ₀′ X = record
          { _⟨$⟩_ = Λ₀ X
          ; cong = λ θ≈θ′ x≈y → cong (f.η _) (Γ.F-resp-≈ (proj₂ x≈y) θ≈θ′ , proj₁ x≈y)
          }

        commute : ∀ {Y Z} (g : Y 𝒞.⇒ Z) → Λ₀′ Y S.∘ Γ.₁ g S.≈ A^B.₁ g S.∘ Λ₀′ Z
        commute {Y} {Z} g {θ} {θ′} θ≈θ′ {X} {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = begin
            f.η X ⟨$⟩ ((Γ.₁ y₁ ⟨$⟩ (Γ.₁ g ⟨$⟩ θ)) , x₁)
          ≈⟨ cong (f.η X) (Γ.F-resp-≈ y₁≈y₂ (Γ.F-resp-≈ 𝒞.Equiv.refl θ≈θ′) , AEquiv.refl) ⟩
            f.η X ⟨$⟩ ((Γ.₁ y₂ ⟨$⟩ (Γ.₁ g ⟨$⟩ θ′)) , x₁)
          ≈⟨ cong (f.η X) (ΓEquivX.sym (Γ.homomorphism ΓEquivZ.refl) , x₁≈x₂) ⟩
            f.η X ⟨$⟩ (Γ.₁ (g 𝒞.∘ y₂) ⟨$⟩ θ′ , x₂)
          ∎
          where open Reasoning (B.₀ X)
                module ΓEquivX = IsEquivalence (Setoid.isEquivalence (Γ.₀ X))
                module ΓEquivZ = IsEquivalence (Setoid.isEquivalence (Γ.₀ Z))
                module AEquiv = IsEquivalence (Setoid.isEquivalence (A.₀ X))

eval : ∀ {A B} → ⊤′ ·′ (A ^′ B) ·′ A ⇒ ⊤′ ·′ B
eval {A} {B} = ntHelper(record
  { η = ϵ
  ; commute = commute
  })
  where module A^B·A = Functor (⊤′ ·′ (A ^′ B) ·′ A)
        module A = Functor A
        module B = Functor (⊤′ ·′ B)

        ϵ : ∀ X → A^B·A.₀ X S.⇒ B.₀ X
        ϵ X = record
          { _⟨$⟩_ = λ γ → NaturalTransformation.η (proj₂ (proj₁ γ)) X ⟨$⟩ ((proj₂ γ) , 𝒞.id)
          ; cong = λ γ≈δ → proj₂ (proj₁ γ≈δ) (proj₂ γ≈δ , IsEquivalence.refl 𝒞.equiv)
          }

        commute : ∀ {X Y} (f : X 𝒞.⇒ Y) → ϵ X S.∘ A^B·A.₁ f S.≈ B.₁ f S.∘ ϵ Y
        commute {X} {Y} f {(tt , x₁) , y₁} {(tt , x₂) , y₂} ((tt , x₁≈x₂) , y₁≈y₂) = begin
            x₁.η X ⟨$⟩ (A.₁ f ⟨$⟩ y₁ , f 𝒞.∘ 𝒞.id )
          ≈⟨
            cong (x₁.η X) ( Setoid.refl (A.₀ X)
                          , 𝒞.Equiv.trans 𝒞.identityʳ (𝒞.Equiv.sym (𝒞.Equiv.trans 𝒞.identityˡ 𝒞.identityˡ))
                          )
          ⟩
            x₁.η X ⟨$⟩ (Functor.₁ (Env A Y) f ⟨$⟩ (y₁ , 𝒞.id))
          ≈⟨ x₁≈x₂ (A.F-resp-≈ 𝒞.Equiv.refl y₁≈y₂ , 𝒞.Equiv.refl) ⟩
            x₂.η X ⟨$⟩ (Functor.₁ (Env A Y) f ⟨$⟩ (y₂ , 𝒞.id))
          ≈⟨ x₂.commute f (Setoid.refl (Functor.₀ (Env A Y) Y)) ⟩
            B.₁ f ⟨$⟩ (x₂.η Y ⟨$⟩ (y₂ , 𝒞.id))
          ∎
          where open Reasoning (B.₀ X)

                module x₁ = NaturalTransformation x₁
                module x₂ = NaturalTransformation x₂

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

  CCC : ContextualCartesianClosed 𝒰
  CCC = record
    { cartesian = CC
    ; Λ = λ {Γ} {A} {B} f → Λ {Γ} {∥ A ∥} {∥ B ∥} f
    ; eval = λ {A} {B} → eval {∥ A ∥} {∥ B ∥}
    ; β = λ {Γ} {A} {B} f x →
      cong (NaturalTransformation.η f _)
        (Setoid.trans ( Functor.F₀ (Γ ·′ ∥ A ∥) _) ((Functor.identity Γ (Setoid.refl (Functor.F₀ Γ _)))
                      , (Setoid.refl (Functor.F₀ ∥ A ∥ _))
                      )
                      x
        )
    ; unique = λ {Γ} {A} {B} {g} {h} → unique {Γ} {∥ A ∥} {∥ B ∥} {g} {h}
    }
    where unique : ∀ {Γ A B} {g : Γ ·′ A ⇒ ⊤′ ·′ B} {h : Γ ⇒ ⊤′ ·′ A ^′ B}
                   → eval ∘ ⟨ h ∘ π , 𝓏 ⟩ ≈ g
                   → h ≈ Λ g
          unique {Γ} {A} {B} {g} {h} ϵ⟨hπ,𝓏⟩≈g {X} {θ} {θ′} θ≈θ′ = tt , I
            where module Γ = Functor Γ
                  module A^B = Functor (A ^′ B)
                  module ⊤·A^B = Functor (⊤′ ·′ A ^′ B)
                  module A = Functor A
                  module B = Functor (⊤′ ·′ B)

                  module h = NaturalTransformation h
                  module Λg = NaturalTransformation (Λ g)

                  I : Setoid._≈_ (A^B.₀ X) (proj₂ (h.η X ⟨$⟩ θ)) (proj₂ (Λg.η X ⟨$⟩ θ′))
                  I {Y} {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = begin
                      NaturalTransformation.η (proj₂ (h.η X ⟨$⟩ θ)) Y ⟨$⟩ (x₁ , y₁)
                    ≈⟨
                      cong (NaturalTransformation.η (proj₂ (h.η X ⟨$⟩ θ)) Y)
                           (Setoid.refl (A.₀ Y) , 𝒞.Equiv.sym 𝒞.identityʳ)
                    ⟩
                      NaturalTransformation.η (proj₂ (h.η X ⟨$⟩ θ)) Y ⟨$⟩ (x₁ , y₁ 𝒞.∘ 𝒞.id)
                    ≡⟨⟩
                      NaturalTransformation.η (proj₂ (⊤·A^B.₁ y₁ ⟨$⟩ (h.η X ⟨$⟩ θ))) Y ⟨$⟩ (x₁ , 𝒞.id)
                    ≈⟨ proj₂ (h.sym-commute y₁ (Setoid.refl (Γ.₀ X))) (Setoid.refl (A.₀ Y) , 𝒞.Equiv.refl) ⟩
                      NaturalTransformation.η (proj₂ (h.η Y ⟨$⟩ (Γ.₁ y₁ ⟨$⟩ θ))) Y ⟨$⟩ (x₁ , 𝒞.id)
                    ≈⟨ ϵ⟨hπ,𝓏⟩≈g ((Γ.F-resp-≈ y₁≈y₂ θ≈θ′) , x₁≈x₂) ⟩
                      NaturalTransformation.η g Y ⟨$⟩ (Γ.₁ y₂ ⟨$⟩ θ′ , x₂)
                    ∎
                    where open Reasoning (B.₀ Y)
