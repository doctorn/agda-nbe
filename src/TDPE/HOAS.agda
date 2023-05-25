module TDPE.HOAS where

open import TDPE.Base

Π : 𝒞 → Set → Set
Π 𝟙       X = X
Π (Γ · A) X = Π Γ (𝔗𝔪 (Γ · A) A → X)

→𝒯 : 𝒞 → 𝒰 ᵀ → 𝒰 ᵀ
→𝒯 𝟙       B = B
→𝒯 (Γ · A) B = →𝒯 Γ (A ⇒ B)

^ : ∀ {Γ B} Δ
    → (Π Δ (𝔗𝔪 (Γ ⊕ Δ) B))
    → 𝔗𝔪 Γ (→𝒯 Δ B)
^ {Γ} {B} Δ f = {!!}
