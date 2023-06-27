{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Relation {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma; CommaObj; Comma⇒)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁; ω₂; 𝒲)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Representation 𝒰 as R using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣)
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

open import Categories.Diagram.Pullback Psh.Psh using (Pullback)

module 𝕎 = Category 𝕎

𝓡₀ : 𝒰ᵀ → Psh.Obj
𝓡 : ℭ → Psh.Obj

↓₀ : ∀ A → 𝓡₀ A Psh.⇒ 𝔑𝔣₀ A
↑₀ : ∀ A → 𝔑𝔢₀ A Psh.⇒ 𝓡₀ A

yoga₀ : ∀ {A} → 𝔦₀ A Psh.∘ ↓₀ A Psh.∘ ↑₀ A Psh.≈ 𝔦₀′ A

module _ A where module 𝓡₀ = Functor (𝓡₀ A)
module _ A where module ↓₀ = NaturalTransformation (↓₀ A)
module _ A where module ↑₀ = NaturalTransformation (↑₀ A)

module _ {A B} where

  ϕ : NaturalTransformation (𝓡₀ A Psh.^ 𝓡₀ B) (𝓡₀ A Psh.^ Tm.₀ (𝟙 · B))
  ϕ = Psh.Λ (𝔦₀ _ Psh.∘ ↓₀ _ Psh.∘ Psh.eval)

  ψ : NaturalTransformation (Tm.₀ (𝟙 · A ⇒ B)) (𝓡₀ A Psh.^ Tm.₀ (𝟙 · B))
  ψ = Psh.Λ (app Psh.∘ Psh.⟨ Psh.π , 𝔦₀ _ Psh.∘ ↓₀ _ Psh.∘ Psh.𝓏 ⟩)
    where app : NaturalTransformation (Tm.₀ (𝟙 · A ⇒ B) Psh.× Tm.₀ (𝟙 · A)) (Tm.₀ (𝟙 · B))
          app = ntHelper (record
            { η = λ Γ → record
              { _⟨$⟩_ = λ { (f , x) → ! ∷ 𝒵 f ⦅ 𝒵 x ⦆ }
              ; cong = λ { (f , x) → ∷-congᵣ (app-cong₂ (𝒵-cong f) (𝒵-cong x)) }
              }
            ; commute = λ g →
              λ { {f₁ , x₁} {f₂ , x₂} (f₁≈f₂ , x₁≈x₂) →
                ∷-congᵣ (C.sym (C.trans v𝓏 (C.trans
                  (sb-congₗ (app-cong₂ (𝒵-cong (S.sym f₁≈f₂)) (𝒵-cong (S.sym x₁≈x₂))))
                  (C.trans sb-app
                    (app-cong₂
                      (C.trans (sb-comp {γ = f₁}) (C.sym v𝒵))
                      (C.trans (sb-comp {γ = x₁}) (C.sym v𝒵)))))))
              }
            })

  module ϕ = NaturalTransformation ϕ
  module ψ = NaturalTransformation ψ

𝓡₀ ` A ` = 𝔑𝔣₀ ` A `
𝓡₀ (A ⇒ B) = Pullback.P (ψ {A} {B} Psh.⊗ ϕ {A} {B})

𝓡 𝟙       = Psh.⊤
𝓡 (Γ · A) = 𝓡 Γ Psh.× 𝓡₀ A

private
  ↑₀-η : ∀ A Δ → Setoid.Carrier (𝔑𝔢₀.₀ A Δ) → Setoid.Carrier (𝓡₀.₀ A Δ)
  ↓₀-η : ∀ A Δ → Setoid.Carrier (𝓡₀.₀ A Δ) → Setoid.Carrier (𝔑𝔣₀.₀ A Δ)

  ↑₀-cong : ∀ A Δ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Δ)}
            → Setoid._≈_ (𝔑𝔢₀.₀ A Δ) x y
            → Setoid._≈_ (𝓡₀.₀ A Δ) (↑₀-η A Δ x) (↑₀-η A Δ y)
  ↓₀-cong : ∀ A Δ {x y : Setoid.Carrier (𝓡₀.₀ A Δ)}
            → Setoid._≈_ (𝓡₀.₀ A Δ) x y
            → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↓₀-η A Δ x) (↓₀-η A Δ y)

  ↑₀-commute : ∀ A {Γ Δ} (w : 𝒲 Δ Γ)
               → ∀ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
               → Setoid._≈_ (𝔑𝔢₀.₀ A Γ) x y
               → Setoid._≈_ (𝓡₀.₀ A Δ) (↑₀-η A Δ (R.+′ w x)) (𝓡₀.₁ A w ⟨$⟩ ↑₀-η A Γ y)
  ↓₀-commute : ∀ A {Γ Δ} (w : 𝒲 Δ Γ)
               → ∀ {x y : Setoid.Carrier (𝓡₀.₀ A Γ)}
               → Setoid._≈_ (𝓡₀.₀ A Γ) x y
               → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↓₀-η A Δ (𝓡₀.₁ A w ⟨$⟩ x)) (R.+ w (↓₀-η A Γ y))

  ↑₀-η ` A `   Δ x = R.ι x
  ↑₀-η (A ⇒ B) Δ x =
    ( 𝔦₀′.η (A ⇒ B) Δ ⟨$⟩ x
    , ntHelper (record
        { η = λ Γ → record
          { _⟨$⟩_ = λ { (y , w) → ↑₀.η B Γ ⟨$⟩ (R.+′ w x R.⦅ ↓₀.η A Γ ⟨$⟩ y ⦆) }
          ; cong = λ { (y , w) →
            cong (↑₀.η B Γ) (PE.cong₂ R._⦅_⦆ (PE.cong₂ R.+′ w PE.refl) (cong (↓₀.η A Γ) y)) }
          }
        ; commute =
          λ {Γ} {Δ} f → λ { {y₁ , w} {y₂ , _} (y₁≈y₂ , PE.refl) →
            Setoid.trans (𝓡₀.₀ B Δ)
              (cong (↑₀.η B Δ)
                (PE.cong₂ R._⦅_⦆
                  (PE.trans (PE.cong₂ R.+′ 𝕎.identityˡ PE.refl) (R.+′-homomorphism PE.refl))
                  (↓₀.commute A f (Setoid.refl (𝓡₀.₀ A Γ)))))
              (↑₀.commute B f (PE.cong₂ R._⦅_⦆ PE.refl (cong (↓₀.η A Γ) y₁≈y₂)))
          }
        })
    )
    , λ { {Γ} {y₁ , w} {y₂ , _} (y₁≈y₂ , PE.refl) →
        S.sym (S.trans
          (yoga₀ PE.refl)
          (∷-congᵣ (app-cong₂
            (C.trans
              (𝒵-cong (cong (𝔦₀′.η (A ⇒ B) Γ) (PE.cong₂ R.+′ (𝕎.identityʳ {f = w}) (PE.refl {x = x}))))
              (𝒵-cong (𝔦₀′.commute (A ⇒ B) w {x} PE.refl)))
            (𝒵-cong (cong (𝔦₀.η A Γ) (cong (↓₀.η A Γ) (Setoid.sym (𝓡₀.₀ A Γ) y₁≈y₂)))))))
      }

  ↓₀-η ` A `   Δ x             = x
  ↓₀-η (A ⇒ B) Δ ((_ , x) , _) =
    R.Λ (↓₀.η B (Δ · A) ⟨$⟩ (x.η (Δ · A) ⟨$⟩ (↑₀.η A (Δ · A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ)))
    where module x = NaturalTransformation x

  ↑₀-cong ` A `   Δ x = PE.cong R.ι x
  ↑₀-cong (A ⇒ B) Δ x =
    ( (cong (𝔦₀′.η (A ⇒ B) Δ) x)
    , λ { {Γ} (y , w) →
        cong (↑₀.η B Γ) (PE.cong₂ R._⦅_⦆ (PE.cong₂ R.+′ w x) (cong (↓₀.η A Γ) y))
      }
    )
    , tt

  ↓₀-cong ` A `   Δ x             = x
  ↓₀-cong (A ⇒ B) Δ ((_ , x) , _) =
    PE.cong R.Λ (cong (↓₀.η B (Δ · A)) (x (cong (↑₀.η A (Δ · A)) PE.refl , PE.refl)))

  ↑₀-commute ` A `   w x = PE.cong R.ι (PE.cong (R.+′ w) x)
  ↑₀-commute (A ⇒ B) w {x} PE.refl =
    ( 𝔦₀′.commute (A ⇒ B) w (PE.refl {x = x})
    , (λ { {Ξ} (y₁≈y₂ , PE.refl) →
      cong (↑₀.η B Ξ) (PE.cong₂ R._⦅_⦆ (PE.sym (R.+′-homomorphism PE.refl)) (cong (↓₀.η A Ξ) y₁≈y₂)) })
    )
    , tt

  ↓₀-commute ` A `   w x = cong (𝓡₀.₁ ` A ` w) x
  ↓₀-commute (A ⇒ B) {Γ} {Δ} w {(_ , x₁) , _} {(_ , x₂) , _} ((_ , x₁≈x₂) , _) = PE.cong R.Λ (begin
      ↓₀.η B (Δ · A) ⟨$⟩ (x₁.η (Δ · A) ⟨$⟩ (↑₀.η A (Δ · A) ⟨$⟩ R.𝓋 R.𝓏 , w 𝕎.∘ ω₁ ϵ))
    ≡⟨ cong (↓₀.η B (Δ · A)) (cong (x₁.η (Δ · A)) (↑₀.commute A (ω₂ w) PE.refl , PE.refl)) ⟩
      ↓₀.η B (Δ · A) ⟨$⟩ (x₁.η (Δ · A) ⟨$⟩ (𝓡₀.₁ A (ω₂ w) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ R.𝓋 R.𝓏) , w 𝕎.∘ ω₁ ϵ))
    ≡⟨ cong (↓₀.η B (Δ · A)) (x₁≈x₂ (Setoid.refl (𝓡₀.₀ A (Δ · A)) , PE.cong ω₁ I)) ⟩
      ↓₀.η B (Δ · A) ⟨$⟩ (x₂.η (Δ · A) ⟨$⟩ (Functor.₁ (𝓡₀ A Psh.× Psh.𝕪.₀ Γ) (ω₂ w) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ)))
    ≡⟨ cong (↓₀.η B (Δ · A)) (x₂.commute (ω₂ w) (Setoid.refl (𝓡₀.₀ A (Γ · A)) , PE.refl)) ⟩
      ↓₀.η B (Δ · A) ⟨$⟩ (𝓡₀.₁ B (ω₂ w) ⟨$⟩ (x₂.η (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ)))
    ≡⟨ ↓₀.commute B (ω₂ w) (Setoid.refl (𝓡₀.₀ B (Γ · A))) ⟩
      R.+ (ω₂ w) (↓₀.η B (Γ · A) ⟨$⟩ (x₂.η (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ R.𝓋 R.𝓏 , ω₁ ϵ)))
    ∎)
    where open PE.≡-Reasoning
          module x₁ = NaturalTransformation x₁
          module x₂ = NaturalTransformation x₂

          I : w 𝕎.∘ ϵ ≡ ϵ 𝕎.∘ (ϵ 𝕎.∘ w)
          I = PE.trans 𝕎.identityʳ (PE.trans (PE.sym 𝕎.identityˡ) (PE.sym 𝕎.identityˡ))

↑₀ A = ntHelper (record
  { η = λ Δ → record
    { _⟨$⟩_ = ↑₀-η A Δ
    ; cong = ↑₀-cong A Δ
    }
  ; commute = ↑₀-commute A
  })

↓₀ A = ntHelper (record
  { η = λ Δ → record
    { _⟨$⟩_ = ↓₀-η A Δ
    ; cong = ↓₀-cong A Δ
    }
  ; commute = ↓₀-commute A
  })

yoga₀ {` A `}         PE.refl = S.refl
yoga₀ {A ⇒ B} {Γ} {x} PE.refl =
  S.trans
    (∷-congᵣ (Λ-cong I))
    (S.sym (ContextualCartesianClosed.η Syntax.CCC (𝔦₀′.η (A ⇒ B) Γ ⟨$⟩ x)))
  where open Reasoning C.setoid

        I = begin
            𝒵 (𝔦₀.η B (Γ · A) ⟨$⟩ (↓₀.η B (Γ · A) ⟨$⟩ (↑₀.η B (Γ · A) ⟨$⟩ (R.+′ (ω₁ ϵ) x R.⦅ ↓₀.η A (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ R.𝓋 R.𝓏) ⦆))))
          ≈⟨ 𝒵-cong (yoga₀ PE.refl) ⟩
            𝒵 (𝔦₀′.η B (Γ · A) ⟨$⟩ (R.+′ (ω₁ ϵ) x R.⦅ ↓₀.η A (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ R.𝓋 R.𝓏) ⦆))
          ≈⟨ app-congᵣ (𝒵-cong (yoga₀ PE.refl)) ⟩
            𝒵 (𝔦₀′.η (A ⇒ B) (Γ · A) ⟨$⟩ (R.+′ (ω₁ ϵ) x)) ⦅ 𝓏 ⦆
          ≈⟨ app-congₗ (𝒵-cong (𝔦₀′.commute (A ⇒ B) (ω₁ (ϵ {Γ})) {x = x} PE.refl)) ⟩
            𝓏 [ (𝔦₀′.η (A ⇒ B) Γ ⟨$⟩ x) ∘ (W.₁ (ϵ {Γ}) ∘ π id) ] ⦅ 𝓏 ⦆
          ≈⟨ app-congₗ (sb-congᵣ (∘-congᵣ (∘-congₗ (W.identity {Γ})))) ⟩
            𝓏 [ (𝔦₀′.η (A ⇒ B) Γ ⟨$⟩ x) ∘ (id ∘ π id) ] ⦅ 𝓏 ⦆
          ≈⟨ app-congₗ (sb-congᵣ (∘-congᵣ ∘-identityˡ)) ⟩
            𝓏 [ (𝔦₀′.η (A ⇒ B) Γ ⟨$⟩ x) ∘ π id ] ⦅ 𝓏 ⦆
          ≈⟨ C.sym (app-cong₂ vp v𝓏) ⟩
            (p 𝓏 [ _ ∷ 𝓏 ]) ⦅ 𝓏 [ _ ∷ 𝓏 ] ⦆
          ≈⟨ C.sym sb-app ⟩
            (p 𝓏 ⦅ 𝓏 ⦆) [ _ ∷ 𝓏 ]
          ∎

↑ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ 𝓡 Δ
↓ : ∀ Δ → 𝓡 Δ Psh.⇒ 𝔑𝔣 Δ

module _ Δ where module ↑ = NaturalTransformation (↑ Δ)
module _ Δ where module ↓ = NaturalTransformation (↓ Δ)

↑ 𝟙       = Psh.!
↑ (Δ · A) = Psh.⟨ ↑ Δ Psh.∘ R.proj 𝔑𝔢₀ , ↑₀ A Psh.∘ R.zero′ 𝔑𝔢₀ ⟩

↓ 𝟙 = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ _ → R.!
    ; cong = λ _ → R.!
    }
  ; commute = λ _ _ → R.!
  })
↓ (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ { (γ , a) → (↓.η Δ Γ ⟨$⟩ γ) R.∷ (↓₀.η A Γ ⟨$⟩ a) }
    ; cong = λ { (γ , a) → cong (↓.η Δ Γ) γ R.∷ cong (↓₀.η A Γ) a }
    }
  ; commute = λ { f (γ , a) → ↓.commute Δ f γ R.∷ ↓₀.commute A f a }
  })

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↓ Δ Psh.∘ ↑ Δ Psh.≈ 𝔦′ Δ
yoga {Δ = 𝟙}     R.!       = !η
yoga {Δ = Δ · A} (γ R.∷ a) = ∷-cong₂ (yoga γ) (𝒵-cong (yoga₀ a))

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


{-
CCC : ContextualCartesianClosed Gl 𝒰
CCC = record
  { cartesian = CC
  ; Λ = λ {Γ} {A} {B} f → record
    { g = {!!}
    ; h = ! ∷ Λ (𝒵 (Comma⇒.h f))
    ; commute = {!!}
    }
  ; eval = {!!} {- λ {A} {B} → record
    { g = Psh.eval
    ; h = ContextualCartesianClosed.eval S.CCC
    ; commute = λ {Γ} {x₁} {x₂} x₁≈x₂ → eval-commute {A} {B} {Γ} {x₁} {x₂} x₁≈x₂
    } -}
  ; β = {!!} {- λ {Γ} {A} {B} f →
    ( ContextualCartesianClosed.β (Psh.CCC λ A₀ → 𝔑𝔣₀ ` A₀ `) {CommaObj.α Γ} {A} {B} (Comma⇒.g f)
    , ContextualCartesianClosed.β S.CCC (Comma⇒.h f)
    ) -}
  ; unique = {!!} {- λ {Γ} {A} {B} {g} {h} x →
    ( ContextualCartesianClosed.unique (Psh.CCC λ A₀ → 𝔑𝔣₀ ` A₀ `)
        {CommaObj.α Γ} {A} {B} {Comma⇒.g g} {Comma⇒.g h} (proj₁ x)
    , ContextualCartesianClosed.unique S.CCC (proj₂ x)
    ) -}
  }
-}

{-
  where Λ-commute : ∀ {Γ A B} f {Δ x₁ x₂} → Setoid._≈_ (Functor.₀ (CommaObj.α Γ) Δ) x₁ x₂ → _
        Λ-commute {Γ} {A} {B} f {Δ} {x₁} {x₂} x₁≈x₂ = S.∷-congᵣ (begin
            S.Λ (S.𝒵 (Comma⇒.h f)) S.[ NaturalTransformation.η (CommaObj.f Γ) Δ ⟨$⟩ x₁ ]
          ≈⟨ S.sb-lam ⟩
            S.Λ (S.𝒵 (Comma⇒.h f) S.[ S.↑[ NaturalTransformation.η (CommaObj.f Γ) Δ ⟨$⟩ x₁ ] ])
          ≈⟨ {!!} ⟩
            S.Λ (S.𝒵 (𝔮B.η (Δ · A) ⟨$⟩ (
              NaturalTransformation.η (Comma⇒.g f) (Δ · A) ⟨$⟩
                ( Functor.F₁ (CommaObj.α Γ) (ω₁ 𝕎.id) ⟨$⟩ x₂
                , ↓₀-η A (Δ · A) (𝓋 𝓏)
                )
            )))
          ∎)
          where open Reasoning S.C.setoid
                module 𝔮B = NaturalTransformation (𝔮 (𝟙 · B))

        eval-commute : ∀ {A B Γ x₁ x₂} → Setoid._≈_ (Functor.₀ (CommaObj.α (⊤′ ·′ A ⇒ B ·′ A)) Γ) x₁ x₂ → _
        eval-commute {A} {B} {Γ} {(_ , f₁) , x₁} {(_ , f₂) , x₂} ((_ , f₁≈f₂) , x₁≈x₂) = S.∷-congᵣ (begin
            (S.p S.𝓏 S.⦅ S.𝓏 ⦆) S.[ α.η Γ ⟨$⟩ ((_ , f₁) , x₁) ]
          ≈⟨ S.sb-app ⟩
            (S.p S.𝓏  S.[ α.η Γ ⟨$⟩ ((_ , f₁) , x₁) ]) S.⦅ S.𝓏 S.[ α.η Γ ⟨$⟩ ((_ , f₁) , x₁) ] ⦆
          ≈⟨ S.app-cong₂ (S.C.trans S.vp S.v𝓏) S.v𝓏 ⟩
            S.Λ (S.𝒵 (𝔮B.η (Γ · A) ⟨$⟩ (f₁.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))) S.⦅ S.𝒵 (𝔮A.η Γ ⟨$⟩ (tt , x₁)) ⦆
          ≈⟨ {!α.η Γ ⟨$⟩ ((_ , f₁) , x₁)!} ⟩
            S.𝒵 (𝔮B.η Γ ⟨$⟩ (f₂.η Γ ⟨$⟩ (x₂ , 𝕎.id)))
          ∎)
          where open Reasoning S.C.setoid
                module 𝔮A = NaturalTransformation (𝔮 (𝟙 · A))
                module 𝔮B = NaturalTransformation (𝔮 (𝟙 · B))
                module f₁ = NaturalTransformation f₁
                module f₂ = NaturalTransformation f₂
                module α = NaturalTransformation (CommaObj.f (⊤′ ·′ A ⇒ B ·′ A))
-}
