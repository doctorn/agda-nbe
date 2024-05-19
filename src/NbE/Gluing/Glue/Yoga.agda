{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Glue.Yoga {a} (𝒰 : Set a) where

open import Function.Equality using (cong; _⟨$⟩_)

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import NbE.Gluing.Contexts 𝒰
open import NbE.Gluing.Glue.Base 𝒰
open import NbE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁; ω₂; 𝒲)
open import NbE.Gluing.Embedding 𝒰
open import NbE.Gluing.Categories.Category.ContextualCartesianClosed
open import NbE.Gluing.Representation 𝒰 as R using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣)
open import NbE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)
import NbE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

open import Categories.Diagram.Pullback Psh.Psh using (Pullback)

module 𝕎 = Category 𝕎

𝓡₀ : 𝒰ᵀ → Psh.Obj
𝓡 : ℭ → Psh.Obj

↓₀ : ∀ A → 𝓡₀ A Psh.⇒ 𝔑𝔣₀ A
↑₀ : ∀ A → 𝔑𝔢₀ A Psh.⇒ 𝓡₀ A

yoga₀ : ∀ {A} → 𝔦₀ A Psh.∘ ↓₀ A Psh.∘ ↑₀ A Psh.≈ 𝔦₀′ A

module _ A where
  module 𝓡₀ = Functor (𝓡₀ A)
  module ↓₀ = NaturalTransformation (↓₀ A)
  module ↑₀ = NaturalTransformation (↑₀ A)

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
            𝓏 [ (𝔦₀′.η (A ⇒ B) Γ ⟨$⟩ x) ∘ (π (E.₁ (ϵ {Γ}))) ] ⦅ 𝓏 ⦆
          ≈⟨ app-congₗ (sb-congᵣ (∘-congᵣ (π-cong E.identity))) ⟩
            𝓏 [ (𝔦₀′.η (A ⇒ B) Γ ⟨$⟩ x) ∘ π id ] ⦅ 𝓏 ⦆
          ≈⟨ C.sym (app-cong₂ vp v𝓏) ⟩
            (p 𝓏 [ _ ∷ 𝓏 ]) ⦅ 𝓏 [ _ ∷ 𝓏 ] ⦆
          ≈⟨ C.sym sb-app ⟩
            (p 𝓏 ⦅ 𝓏 ⦆) [ _ ∷ 𝓏 ]
          ∎

↑ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ 𝓡 Δ
↓ : ∀ Δ → 𝓡 Δ Psh.⇒ 𝔑𝔣 Δ

module _ Δ where
  module ↑ = NaturalTransformation (↑ Δ)
  module ↓ = NaturalTransformation (↓ Δ)
  module 𝓡 = Functor (𝓡 Δ)

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

𝔦′-id : ∀ Γ → 𝔦′.η Γ Γ ⟨$⟩ R.identity Γ S.≈ id
𝔦′-id 𝟙       = !η
𝔦′-id (Γ · A) =
  ∷-congₗ (S.trans
    (𝔦′.commute Γ (ω₁ ϵ) (Setoid.refl (𝔑𝔢.₀ Γ Γ)))
    (S.trans ∘-identityˡ
      (S.trans
        (∘-congᵣ (π-cong E.identity))
        (S.trans π-id (π-cong (𝔦′-id Γ))))))
