{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Glue.Relation {a} (𝒰 : Set a) where

open import Function.Equality

open import Data.Product using (_,_; proj₁; proj₂)

open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (ntHelper; NTHelper; NaturalTransformation)
open import Categories.Category.Construction.Comma using (Comma)

open import Relation.Binary using (Setoid)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Glue.Base 𝒰
open import TDPE.Gluing.Weakenings 𝒰 using (𝕎; ϵ; ω₁; ω₂; 𝒲)
open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Representation 𝒰 as Repr
  using (𝔑𝔢₀; 𝔑𝔣₀; 𝔑𝔢; 𝔑𝔣; 𝓋; 𝓏; π; ι; Λ; _⦅_⦆)
import TDPE.Gluing.Syntax 𝒰 as S
import TDPE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

{-
𝓡₀ : 𝒰ᵀ → Psh.Obj

↓₀ : ∀ A → 𝓡₀ A Psh.⇒ 𝔑𝔣₀ A
↑₀ : ∀ A → 𝔑𝔢₀ A Psh.⇒ 𝓡₀ A

yoga₀ : ∀ {A} → 𝔦₀ A Psh.∘ ↓₀ A Psh.∘ ↑₀ A Psh.≈ 𝔦₀′ A

module _ A where module 𝓡₀ = Functor (𝓡₀ A)
module _ A where module ↓₀ = NaturalTransformation (↓₀ A)
module _ A where module ↑₀ = NaturalTransformation (↑₀ A)

module _ {A B} where

  ϕ : NaturalTransformation (𝓡₀ A Psh.^′ 𝓡₀ B) (𝓡₀ A Psh.^′ Tm.₀ (𝟙 · B))
  ϕ = Psh.Λ (𝔦₀ _ Psh.∘ ↓₀ _ Psh.∘ Psh.eval′)

  ψ : NaturalTransformation (Tm.₀ (𝟙 · A ⇒ B)) (𝓡₀ A Psh.^′ Tm.₀ (𝟙 · B))
  ψ = Psh.Λ (app Psh.∘ Psh.⟨ Psh.π , Psh.↑ Psh.∘ 𝔦₀ _ Psh.∘ ↓₀ _ Psh.∘ Psh.𝓏′ ⟩)
    where app : NaturalTransformation (Tm.₀ (𝟙 · A ⇒ B) Psh.·′ Tm.₀ (𝟙 · A)) (Tm.₀ (𝟙 · B))
          app = ntHelper (record
            { η = λ Γ → record
              { _⟨$⟩_ = λ { (f , x) → S.! S.∷ S.𝒵 f S.⦅ S.𝒵 x ⦆ }
              ; cong = λ { (f , x) → S.∷-congᵣ (S.app-cong₂ (S.𝒵-cong f) (S.𝒵-cong x)) }
              }
            ; commute = λ g → λ { (f , x) → {!!} }
            })

  module ϕ = NaturalTransformation ϕ
  module ψ = NaturalTransformation ψ

𝓡₀ ` A ` = 𝔑𝔣₀ ` A `
𝓡₀ (A ⇒ B) = {!!}

↑₀ ` A ` = {!!}
↑₀ (A ⇒ B) = {!!}

↓₀ ` A ` = {!!}
↓₀ (A ⇒ B) = {!!}

yoga₀ {` A `} = {!!}
yoga₀ {A ⇒ B} = {!!}
-}

{-
𝓡₀ : 𝒰ᵀ → Psh.Obj
𝓡₀ A = ⟦ A ⟧ᵀ (λ A₀ → 𝔑𝔣₀ ` A₀ `) {!!}

𝓡 : ℭ → Psh.Obj
𝓡 Γ = ⟦ Γ ⟧ᶜ (λ A₀ → 𝔑𝔣₀ ` A₀ `) {!!} Psh.⊤′ Psh._·′_

module 𝕎 = Category 𝕎

private
  ↑₀-η : ∀ A Δ → Setoid.Carrier (𝓡₀.₀ A Δ) → Setoid.Carrier (𝔑𝔣₀.₀ A Δ)
  ↓₀-η : ∀ A Δ → Setoid.Carrier (𝔑𝔢₀.₀ A Δ) → Setoid.Carrier (𝓡₀.₀ A Δ)

  ↑₀-cong : ∀ A Δ {x y : Setoid.Carrier (𝓡₀.₀ A Δ)}
            → Setoid._≈_ (𝓡₀.₀ A Δ) x y
            → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↑₀-η A Δ x) (↑₀-η A Δ y)
  ↓₀-cong : ∀ A Δ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Δ)}
            → Setoid._≈_ (𝔑𝔢₀.₀ A Δ) x y
            → Setoid._≈_ (𝓡₀.₀ A Δ) (↓₀-η A Δ x) (↓₀-η A Δ y)

  ↑₀-commute : ∀ A {Γ Δ} (w : 𝒲 Δ Γ)
               → ∀ {x y : Setoid.Carrier (𝓡₀.₀ A Γ)}
               → Setoid._≈_ (𝓡₀.₀ A Γ) x y
               → Setoid._≈_ (𝔑𝔣₀.₀ A Δ) (↑₀-η A Δ (𝓡₀.₁ A w ⟨$⟩ x)) (Repr.+ w (↑₀-η A Γ y))
  ↓₀-commute : ∀ A {Γ Δ} (w : 𝒲 Δ Γ)
               → ∀ {x y : Setoid.Carrier (𝔑𝔢₀.₀ A Γ)}
               → Setoid._≈_ (𝔑𝔢₀.₀ A Γ) x y
               → Setoid._≈_ (𝓡₀.₀ A Δ) (↓₀-η A Δ (Repr.+′ w x)) (𝓡₀.₁ A w ⟨$⟩ ↓₀-η A Γ y)

  ↑₀-η ` A `   Δ x = x
  ↑₀-η (A ⇒ B) Δ x = Λ (↑₀-η B (Δ · A) (proj₂ (x.η (Δ · A) ⟨$⟩ (↓₀-η A (Δ · A) (𝓋 𝓏) , ω₁ 𝕎.id))))
    where module x = NaturalTransformation x

  ↑₀-cong ` A `   Δ x = x
  ↑₀-cong (A ⇒ B) Δ x =
    PE.cong Λ (↑₀-cong B (Δ · A) (proj₂ (x (↓₀-cong A (Δ · A) PE.refl , PE.refl))))

  ↑₀-commute ` A `   w x = cong (𝓡₀.₁ ` A ` w) x
  ↑₀-commute (A ⇒ B) {Γ} {Δ} w {x₁} {x₂} x₁≈x₂ = begin
      Λ (↑₀-η B (Δ · A) (proj₂ (x₁.η (Δ · A) ⟨$⟩ (↓₀-η A (Δ · A) (𝓋 𝓏) , w 𝕎.∘ ω₁ 𝕎.id))))
    ≡⟨ PE.cong Λ (↑₀-cong B (Δ · A) (proj₂ (cong (x₁.η (Δ · A)) (↓₀-commute A (ω₂ w) PE.refl , PE.refl)))) ⟩
      Λ (↑₀-η B (Δ · A) (proj₂ (x₁.η (Δ · A) ⟨$⟩ (𝓡₀.₁ A (ω₂ w) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏)) , w 𝕎.∘ ω₁ 𝕎.id))))
    ≡⟨ PE.cong Λ (↑₀-cong B (Δ · A) (proj₂ (x₁≈x₂ (Setoid.refl (𝓡₀.₀ A (Δ · A)) , PE.cong ω₁ I)))) ⟩
      Λ (↑₀-η B (Δ · A) (proj₂ (x₂.η (Δ · A) ⟨$⟩ (Functor.₁ (𝓡₀ A Psh.·′ Psh.𝕪.₀ Γ) (ω₂ w) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ≡⟨
      PE.cong Λ
        (↑₀-cong B (Δ · A) (NaturalTransformation.commute (Psh.↓ Psh.∘ x₂) (ω₂ w)
          (Setoid.refl (𝓡₀.₀ A (Γ · A)) , PE.refl)))
    ⟩
      Λ (↑₀-η B (Δ · A) (𝓡₀.₁ B (ω₂ w) ⟨$⟩ (proj₂ (x₂.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ≡⟨ PE.cong Λ (↑₀-commute B (ω₂ w) (Setoid.refl (𝓡₀.₀ B (Γ · A)))) ⟩
      Λ (Repr.+ (ω₂ w) (↑₀-η B (Γ · A) (proj₂ (x₂.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ≡⟨⟩
      Repr.+ w (Λ (↑₀-η B (Γ · A) (proj₂ (x₂.η (Γ · A) ⟨$⟩ (↓₀-η A (Γ · A) (𝓋 𝓏) , ω₁ 𝕎.id)))))
    ∎
    where open PE.≡-Reasoning
          module x₁ = NaturalTransformation x₁
          module x₂ = NaturalTransformation x₂

          I : w 𝕎.∘ 𝕎.id ≡ 𝕎.id 𝕎.∘ (𝕎.id 𝕎.∘ w)
          I = begin
              w 𝕎.∘ 𝕎.id
            ≡⟨ 𝕎.identityʳ ⟩
              w
            ≡⟨ PE.sym 𝕎.identityˡ ⟩
              𝕎.id 𝕎.∘ w
            ≡⟨ PE.sym 𝕎.identityˡ ⟩
              𝕎.id 𝕎.∘ (𝕎.id 𝕎.∘ w)
            ∎

  ↓₀-η ` A `   Δ x = ι x
  ↓₀-η (A ⇒ B) Δ x = ntHelper (record
    { η = λ Γ → record
      { _⟨$⟩_ = λ e → tt , ↓₀-η B Γ (Repr.+′ (proj₂ e) x ⦅ ↑₀-η A Γ (proj₁ e) ⦆)
      ; cong = λ e → tt , ↓₀-cong B Γ
        (PE.cong₂ _⦅_⦆ (PE.cong₂ Repr.+′ (proj₂ e) PE.refl) (↑₀-cong A Γ (proj₁ e)))
      }
    ; commute = λ {Γ} {Δ} f →
      λ { {y₁ , w} {y₂ , _} (y₁≈y₂ , PE.refl)
        → tt , Setoid.trans (𝓡₀.₀ B Δ)
          (↓₀-cong B Δ
            (PE.cong₂ _⦅_⦆
              (PE.trans
                  (PE.cong₂ Repr.+′ 𝕎.identityˡ PE.refl)
                  (Repr.+′-homomorphism PE.refl)
              )
              (↑₀-commute A f (Setoid.refl (𝓡₀.₀ A Γ)))
            )
          )
          (↓₀-commute B f (PE.cong₂ _⦅_⦆ PE.refl (↑₀-cong A Γ y₁≈y₂)))
      }
    })

  ↓₀-cong ` A `   Δ x = PE.cong ι x
  ↓₀-cong (A ⇒ B) Δ x {Γ} (y , w) =
    tt , ↓₀-cong B Γ (PE.cong₂ _⦅_⦆ (PE.cong₂ Repr.+′ w x) (↑₀-cong A Γ y))

  ↓₀-commute ` A `   w x = PE.cong ι (PE.cong (Repr.+′ w) x)
  ↓₀-commute (A ⇒ B) w PE.refl {Ξ} (y₁≈y₂ , PE.refl) =
    tt , ↓₀-cong B Ξ (PE.cong₂ _⦅_⦆ (PE.sym (Repr.+′-homomorphism PE.refl)) (↑₀-cong A Ξ y₁≈y₂))

↑₀ : ∀ A → 𝓡₀ A Psh.⇒ 𝔑𝔣₀ A
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

↑ : ∀ Δ → 𝓡 Δ Psh.⇒ 𝔑𝔣 Δ
↑ 𝟙 = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ _ → Repr.!
    ; cong = λ _ → Repr.!
    }
  ; commute = λ _ _ → Repr.!
  })
↑ (Δ · A) = ntHelper (record
  { η = λ Γ → record
    { _⟨$⟩_ = λ x → (↑Δ.η Γ ⟨$⟩ proj₁ x) Repr.∷ ↑₀-η A Γ (proj₂ x)
    ; cong = λ x → cong (↑Δ.η Γ) (proj₁ x) Repr.∷ ↑₀-cong A Γ (proj₂ x)
    }
  ; commute = λ f x → ↑Δ.commute f (proj₁ x) Repr.∷ ↑₀-commute A f (proj₂ x)
  })
  where module ↑Δ = NaturalTransformation (↑ Δ)

↓ : ∀ Δ → 𝔑𝔢 Δ Psh.⇒ 𝓡 Δ
↓ 𝟙       = Psh.!
↓ (Δ · A) = Psh.⟨ ↓ Δ Psh.∘ Repr.proj 𝔑𝔢₀ , Psh.↑ Psh.∘ ↓₀ A Psh.∘ Repr.zero′ 𝔑𝔢₀ ⟩

𝔮 : ∀ Δ → 𝓡 Δ Psh.⇒ Functor.₀ Tm Δ
𝔮 Δ = 𝔦 Δ Psh.∘ ↑ Δ

yoga₀ : ∀ {A} → 𝔦₀ A Psh.∘ ↑₀ A Psh.∘ ↓₀ A Psh.≈ 𝔦₀′ A
yoga₀ {A = ` A `} PE.refl = S.S.refl
yoga₀ {A = A ⇒ B} {Γ} {x} {_} PE.refl =
  S.S.trans
    (S.∷-congᵣ (S.Λ-cong I))
    (S.S.sym (ContextualCartesianClosed.η S.CCC (𝔦₀′-η (A ⇒ B) Γ x)))
  where open Reasoning S.C.setoid

        I = begin
            S.𝒵 (𝔦₀-η B (Γ · A) (↑₀-η B (Γ · A) (↓₀-η B (Γ · A) (Repr.+′ (ω₁ (𝕎.id)) x ⦅ ↑₀-η A (Γ · A) (↓₀-η A (Γ · A) (𝓋 𝓏)) ⦆))))
          ≈⟨ S.𝒵-cong (yoga₀ PE.refl) ⟩
            S.𝒵 (𝔦₀′-η B (Γ · A) (Repr.+′ (ω₁ (𝕎.id)) x ⦅ ↑₀-η A (Γ · A) (↓₀-η A (Γ · A) (𝓋 𝓏)) ⦆))
          ≈⟨ S.app-congᵣ (S.𝒵-cong (yoga₀ PE.refl)) ⟩
            S.𝒵 (𝔦₀′-η (A ⇒ B) (Γ · A) (Repr.+′ (ω₁ 𝕎.id) x)) S.⦅ S.𝓏 ⦆
          ≈⟨ S.app-congₗ (S.𝒵-cong (NaturalTransformation.commute (𝔦₀′ (A ⇒ B)) (ω₁ (𝕎.id {Γ})) {x = x} PE.refl)) ⟩
            S.𝓏 S.[ 𝔦₀′-η (A ⇒ B) Γ x S.∘ (W.₁ (𝕎.id {Γ}) S.∘ S.π S.id) ] S.⦅ S.𝓏 ⦆
          ≈⟨ S.app-congₗ (S.sb-congᵣ (S.∘-congᵣ (S.∘-congₗ (W.identity {Γ})))) ⟩
            S.𝓏 S.[ 𝔦₀′-η (A ⇒ B) Γ x S.∘ (S.id S.∘ S.π S.id) ] S.⦅ S.𝓏 ⦆
          ≈⟨ S.app-congₗ (S.sb-congᵣ (S.∘-congᵣ S.∘-identityˡ)) ⟩
            S.𝓏 S.[ 𝔦₀′-η (A ⇒ B) Γ x S.∘ S.π S.id ] S.⦅ S.𝓏 ⦆
          ≈⟨ S.C.sym (S.app-cong₂ S.vp S.v𝓏) ⟩
            (S.p S.𝓏 S.[ _ S.∷ S.𝓏 ]) S.⦅ S.𝓏 S.[ _ S.∷ S.𝓏 ] ⦆
          ≈⟨ S.C.sym S.sb-app ⟩
            (S.p S.𝓏 S.⦅ S.𝓏 ⦆) S.[ _ S.∷ S.𝓏 ]
          ∎

yoga : ∀ {Δ} → 𝔦 Δ Psh.∘ ↑ Δ Psh.∘ ↓ Δ Psh.≈ 𝔦′ Δ
yoga {Δ = 𝟙}     Repr.!       = S.!η
yoga {Δ = Δ · A} (γ Repr.∷ a) = S.∷-cong₂ (yoga γ) (S.𝒵-cong (yoga₀ a))

⊤′ : Gl.Obj
⊤′ = record
  { α = 𝓡 𝟙
  ; β = 𝟙
  ; f = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = λ _ → S.!
      ; cong = λ _ → S.!η
      }
    ; commute = λ _ _ → S.!η
    })
  }

infixl 6 _·′_

_·′_ : Gl.Obj → 𝒰ᵀ → Gl.Obj
Γ ·′ A = record
  { α = CommaObj.α Γ Psh.·′ 𝓡₀ A
  ; β = CommaObj.β Γ · A
  ; f = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = λ x →
        (NaturalTransformation.η (CommaObj.f Γ) X ⟨$⟩ proj₁ x)
          S.∷ S.𝒵 (NaturalTransformation.η (𝔮 (𝟙 · A)) X ⟨$⟩ (tt , proj₂ x))
      ; cong = λ x≈y →
        S.∷-cong₂ (cong (NaturalTransformation.η (CommaObj.f Γ) X) (proj₁ x≈y))
                  (S.𝒵-cong (cong (NaturalTransformation.η (𝔮 (𝟙 · A)) X) (tt , proj₂ x≈y)))
      }
    ; commute = λ f → λ { {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.∷-cong₂ (S.S.trans (S.S.trans (NaturalTransformation.commute (CommaObj.f Γ) f γ₁≈γ₂) S.∘-identityˡ ) (S.S.sym S.πβ′))
        (S.C.trans (S.C.trans (S.𝒵-cong (NaturalTransformation.commute (𝔮 (𝟙 · A)) f (tt , a₁≈a₂))) S.v𝓏) (S.C.sym S.v𝓏)) }
    })
  }

CC : ContextualCartesian Gl 𝒰ᵀ
CC = record
  { terminal = record
    { ⊤ = ⊤′
    ; ⊤-is-terminal = record
      { ! = record
        { g = Psh.!
        ; h = S.!
        ; commute = λ _ → S.!η
        }
      ; !-unique = λ f → Psh.!-unique (Comma⇒.g f) , S.S.sym S.!η
      }
    }
  ; _·_ = _·′_
  ; π = λ {Δ} → record
    { g = Psh.π
    ; h = S.π S.id
    ; commute = λ { {Γ} {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.S.trans S.πβ′ (cong (NaturalTransformation.η (CommaObj.f Δ) Γ) γ₁≈γ₂) }
    }
  ; 𝓏 = λ {_} {A} → record
    { g = Psh.𝓏
    ; h = S.! S.∷ S.𝓏
    ; commute = λ { {Γ} {γ₁ , a₁} {γ₂ , a₂} (γ₁≈γ₂ , a₁≈a₂) →
      S.∷-congᵣ (S.C.trans S.v𝓏 (S.𝒵-cong (cong (NaturalTransformation.η (𝔮 (𝟙 · A)) Γ) (tt , a₁≈a₂)))) }
    }
  ; extensions = λ {Γ} {A} → record
    { ⟨_,_⟩ = λ {Δ} γ a → record
      { g = Psh.⟨ Comma⇒.g γ , Comma⇒.g a ⟩
      ; h = Comma⇒.h γ S.∷ S.𝒵 (Comma⇒.h a)
      ; commute = λ {Γ′} {δ} {δ′} δ≈δ′ →
        S.∷-cong₂ (Comma⇒.commute γ δ≈δ′)
                  (S.C.trans (S.sb-comp {γ = Comma⇒.h a}) (S.𝒵-cong (Comma⇒.commute a δ≈δ′)))
      }
    ; project₁ = λ {Γ} {h} {i} →
      ( (λ {Δ} x → cong (NaturalTransformation.η (Comma⇒.g h) Δ) x)
      , S.πβ′
      )
    ; project₂ = λ {Γ} {h} {i} →
      ( (λ {Δ} x → tt , proj₂ (cong (NaturalTransformation.η (Comma⇒.g i) Δ) x))
      , S.S.trans (S.∷-congᵣ S.v𝓏) S.𝒵η
      )
    ; unique = λ {Δ} {h} {i} {j} x y →
      ( ContextualCartesian.Ext.unique (Psh.CC λ A₀ → 𝔑𝔣₀ ` A₀ `)
          {CommaObj.α Γ} {A} {h = Comma⇒.g h} {Comma⇒.g i} {Comma⇒.g j} (proj₁ x) (proj₁ y)
      , ContextualCartesian.Ext.unique S.CC (proj₂ x) (S.S.trans (proj₂ y) (S.S.sym S.𝒵η))
      )
    }
  }


CCC : ContextualCartesianClosed Gl 𝒰
CCC = record
  { cartesian = CC
  ; Λ = λ {Γ} {A} {B} f → record
    { g = Psh.Λ (Comma⇒.g f)
    ; h = S.! S.∷ S.Λ (S.𝒵 (Comma⇒.h f))
    ; commute = λ {Δ} {x₁} {x₂} x₁≈x₂ → Λ-commute {Γ} {A} {B} f {Δ} {x₁} {x₂} x₁≈x₂
    }
  ; eval = λ {A} {B} → record
    { g = Psh.eval
    ; h = ContextualCartesianClosed.eval S.CCC
    ; commute = λ {Γ} {x₁} {x₂} x₁≈x₂ → eval-commute {A} {B} {Γ} {x₁} {x₂} x₁≈x₂
    }
  ; β = λ {Γ} {A} {B} f →
    ( ContextualCartesianClosed.β (Psh.CCC λ A₀ → 𝔑𝔣₀ ` A₀ `) {CommaObj.α Γ} {A} {B} (Comma⇒.g f)
    , ContextualCartesianClosed.β S.CCC (Comma⇒.h f)
    )
  ; unique = λ {Γ} {A} {B} {g} {h} x →
    ( ContextualCartesianClosed.unique (Psh.CCC λ A₀ → 𝔑𝔣₀ ` A₀ `)
        {CommaObj.α Γ} {A} {B} {Comma⇒.g g} {Comma⇒.g h} (proj₁ x)
    , ContextualCartesianClosed.unique S.CCC (proj₂ x)
    )
  }
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
