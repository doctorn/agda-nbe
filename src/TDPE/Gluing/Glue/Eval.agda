{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Eval {a} (𝒰 : Set a) where

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
open import TDPE.Gluing.Glue.Yoga 𝒰 using (↓₀; ↑₀; 𝓡₀; yoga₀)
open import TDPE.Gluing.Glue.Cartesian 𝒰 using (⊤; _×_)
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁; ω₂; 𝒲)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Representation 𝒰 as R using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣)
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

open import Categories.Diagram.Pullback Psh.Psh using (Pullback)

module 𝕎 = Category 𝕎

module _ {A B} where
  module A⇒B×A = Functor (CommaObj.α ((⊤ × A ⇒ B) × A))

  module _ {Γ} {α₁ α₂ : Setoid.Carrier (A⇒B×A.₀ Γ)} where
    private
      f₁ = proj₂ (proj₁ α₁)
      f₂ = proj₂ (proj₁ α₂)

      module f₁ = NaturalTransformation (proj₂ (proj₁ f₁))
      module f₂ = NaturalTransformation (proj₂ (proj₁ f₂))

      f₁′ = proj₁ (proj₁ f₁)
      f₂′ = proj₁ (proj₁ f₂)

      x₁ = proj₂ α₁
      x₂ = proj₂ α₂

      γ = 𝔦₀.η B (Γ · A) ⟨$⟩ (↓₀.η B (Γ · A) ⟨$⟩ (f₁.η (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ (R.𝓋 R.𝓏) , ω₁ ϵ)))
      δ = 𝔦₀.η A Γ ⟨$⟩ (↓₀.η A Γ ⟨$⟩ x₁)

    eval-commute : Setoid._≈_ (A⇒B×A.₀ Γ) α₁ α₂
                   → ! ∷ (p 𝓏 ⦅ 𝓏 ⦆) [ ! ∷ Λ (𝒵 γ) ∷ 𝒵 δ ]
                     S.≈ ! ∷ 𝒵 (𝔦₀.η B Γ ⟨$⟩ (↓₀.η B Γ ⟨$⟩ (f₂.η Γ ⟨$⟩ (x₂ , ϵ))))
    eval-commute ((tt , ((f₁′≈f₂′ , f₁≈f₂) , tt)) , x₁≈x₂) = ∷-congᵣ (begin
        (p 𝓏 ⦅ 𝓏 ⦆) [ _ ]
      ≈⟨ sb-app ⟩
        (p 𝓏 [ _ ]) ⦅ 𝓏 [ _ ] ⦆
      ≈⟨ app-cong₂ (C.trans vp v𝓏) v𝓏 ⟩
        (Λ (𝒵 γ)) ⦅ 𝒵 δ ⦆
      ≈⟨
        app-congₗ (Λ-cong (𝒵-cong (cong (𝔦₀.η B (Γ · A)) (cong (↓₀.η B (Γ · A)) (cong (f₁.η (Γ · A))
          (Setoid.refl (𝓡₀.₀ A (Γ · A)) , PE.cong ω₁ (PE.sym 𝕎.identity²)))))))
      ⟩
        (Λ (𝒵 (𝔦₀.η B (Γ · A) ⟨$⟩ (↓₀.η B (Γ · A) ⟨$⟩ (f₁.η (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ (R.𝓋 R.𝓏) , ω₁ _)))))) ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (Λ-cong (𝒵-cong (S.sym (proj₂ f₁ (cong (↑₀.η A (Γ · A)) PE.refl , PE.refl {x = ω₁ (ϵ {Γ})}))))) ⟩
        (Λ (𝓏 [ f₁′ ∘ W.₁ (ω₁ (ϵ {Γ})) ] ⦅ 𝒵 (𝔦₀.η A (Γ · A) ⟨$⟩ (↓₀.η A (Γ · A) ⟨$⟩ (↑₀.η A (Γ · A) ⟨$⟩ (R.𝓋 R.𝓏)))) ⦆)) ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (Λ-cong (app-congᵣ (𝒵-cong (yoga₀ PE.refl)))) ⟩
        (Λ (𝓏 [ f₁′ ∘ W.₁ (ω₁ (ϵ {Γ})) ] ⦅ 𝓏 ⦆)) ⦅ 𝒵 δ ⦆
      ≈⟨ Λβ ⟩
        𝓏 [ f₁′ ∘ W.₁ (ω₁ (ϵ {Γ})) ] ⦅ 𝓏 ⦆ [ id ∷ 𝒵 δ ]
      ≈⟨ sb-app ⟩
        (𝓏 [ f₁′ ∘ W.₁ (ω₁ (ϵ {Γ})) ] [ id ∷ 𝒵 δ ]) ⦅ 𝓏 [ id ∷ 𝒵 δ ] ⦆
      ≈⟨ app-cong₂ sb-assoc v𝓏 ⟩
        𝓏 [ (f₁′ ∘ W.₁ (ω₁ (ϵ {Γ}))) ∘ (id ∷ 𝒵 δ) ] ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (sb-congᵣ ∘-assoc) ⟩
        𝓏 [ f₁′ ∘ (W.₁ (ω₁ (ϵ {Γ})) ∘ (id ∷ 𝒵 δ)) ] ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (sb-congᵣ (∘-congᵣ (S.trans (∘-congₗ (S.trans (∘-congₗ (W.identity {A = Γ})) ∘-identityˡ)) (S.trans πβ ∘-identityʳ)))) ⟩
        𝓏 [ f₁′ ∘ id ] ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (sb-congᵣ ∘-identityʳ) ⟩
        𝓏 [ f₁′ ] ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (sb-congᵣ f₁′≈f₂′) ⟩
        𝓏 [ f₂′ ] ⦅ 𝒵 δ ⦆
      ≈⟨ app-congₗ (C.sym (sb-congᵣ (S.trans (∘-congᵣ (W.identity {A = Γ})) ∘-identityʳ))) ⟩
        𝓏 [ f₂′ ∘ W.₁ {A = Γ} ϵ ] ⦅ 𝒵 δ ⦆
      ≈⟨ 𝒵-cong (proj₂ f₂ (x₁≈x₂ , PE.refl)) ⟩
        𝒵 (𝔦₀.η B Γ ⟨$⟩ (↓₀.η B Γ ⟨$⟩ (f₂.η Γ ⟨$⟩ (x₂ , _))))
      ≈⟨ 𝒵-cong (cong (𝔦₀.η B Γ) (cong (↓₀.η B Γ) (cong (f₂.η Γ) (Setoid.refl (𝓡₀.₀ A Γ) , 𝕎.identity²)))) ⟩
        𝒵 (𝔦₀.η B Γ ⟨$⟩ (↓₀.η B Γ ⟨$⟩ (f₂.η Γ ⟨$⟩ (x₂ , ϵ))))
      ∎)
      where open Reasoning C.setoid

  eval : ⊤ × (A ⇒ B) × A Gl.⇒ ⊤ × B
  eval = record
    { g = ntHelper (record
      { η = λ Γ → record
        { _⟨$⟩_ = λ { ((tt , ((_ , f) , _)) , x) → tt , NaturalTransformation.η f Γ ⟨$⟩ (x , ϵ) }
        ; cong = λ { ((tt , ((_ , f) , _)) , x) → tt , f (x , PE.refl) }
        }
      ; commute = λ { g {(tt , ((_ , f₁) , _)) , x₁} {(tt , ((_ , f₂) , _)) , x₂} ((tt , ((_ , f₁≈f₂) , _)) , x₁≈x₂) →
        tt , (Setoid.trans (𝓡₀.₀ B _)
          (f₁≈f₂ ((Setoid.refl (𝓡₀.₀ A _)) , PE.trans 𝕎.identityʳ (PE.sym (PE.trans 𝕎.identityˡ 𝕎.identityˡ))))
          (NaturalTransformation.commute f₂ g (x₁≈x₂ , PE.refl))) }
      })
    ; h = ContextualCartesianClosed.eval Syntax.CCC
    ; commute = λ {Γ} {x₁} {x₂} x₁≈x₂ → eval-commute {Γ} {x₁} {x₂} x₁≈x₂
    }
