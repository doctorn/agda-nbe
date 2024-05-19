{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Embedding {a} (𝒰 : Set a) where

import Relation.Binary.PropositionalEquality as PE

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import NbE.Gluing.Contexts 𝒰
open import NbE.Gluing.Weakenings 𝒰 using (𝕎; ϵ₀; ϵ; ω₁; ω₂)
open import NbE.Gluing.Syntax 𝒰

private
  module 𝕎 = Category 𝕎
  module 𝕋𝕞 = Category 𝕋𝕞

E : Functor 𝕎 𝕋𝕞
E = record
  { F₀ = λ Γ → Γ
  ; F₁ = E₁
  ; identity = E-identity
  ; homomorphism = λ {_} {_} {_} {f} {g} → E-homomorphism {w₁ = f} {g}
  ; F-resp-≈ = λ { PE.refl → S.refl }
  }
  where E₁ : ∀ {Δ Γ} →  Δ 𝕎.⇒ Γ → Δ 𝕋𝕞.⇒ Γ
        E₁ ϵ₀     = 𝔗𝔪.!
        E₁ (ω₁ w) = π (E₁ w)
        E₁ (ω₂ w) = π (E₁ w) ∷ 𝓏

        E-identity : ∀ {Δ} → E₁ (ϵ {Δ}) S.≈ id
        E-identity {𝟙}     = S.refl
        E-identity {Δ · A} = ∷-congₗ (π-cong E-identity)

        E-homomorphism : ∀ {Ξ Δ Γ} {w₁ : Ξ 𝕎.⇒ Δ} {w₂ : Δ 𝕎.⇒ Γ}
                         → E₁ (w₂ 𝕎.∘ w₁) S.≈ E₁ w₂ ∘ E₁ w₁
        E-homomorphism {w₁ = ϵ₀}    {w₂}    = S.sym ∘-identityʳ
        E-homomorphism {w₁ = ω₁ w₁} {w₂}    =
          S.trans (π-cong (E-homomorphism {w₁ = w₁} {w₂})) (S.sym π-lemma)
        E-homomorphism {w₁ = ω₂ w₁} {ω₁ w₂} =
          S.trans
            (S.trans (π-cong (E-homomorphism {w₁ = w₁} {w₂})) (S.sym π-lemma))
            (S.sym πβ)
        E-homomorphism {w₁ = ω₂ w₁} {ω₂ w₂} =
          ∷-cong₂
            (S.trans
              (π-cong (E-homomorphism {w₁ = w₁} {w₂}))
              (S.trans (S.sym π-lemma) (S.sym πβ)))
            (C.sym v𝓏)

module E = Functor E
