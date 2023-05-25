module TDPE.Base where

data 𝒰 : Set where
  ℴ : 𝒰

open import TDPE.Types public
open import TDPE.Contexts (𝒰 ᵀ) public

𝒪 : 𝒰 ᵀ
𝒪 = ` ℴ `

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂; _,_)

𝓐⟦_⟧ᵀ : 𝒰 ᵀ → Set
𝓐⟦ τ ⟧ᵀ = ⟦ τ ⟧ᵀ (λ _ → ℕ) _×_ λ A B → A → B

𝓐⟦_⟧𝒞 : 𝒞 → Set
𝓐⟦_⟧𝒞 = ⟨ 𝓐⟦_⟧ᵀ ⟩

data 𝔗𝔪 : 𝒞 → 𝒰 ᵀ → Set where
  -- variables
  𝓏     : ∀ {Γ A} → 𝔗𝔪 (Γ · A) A
  π     : ∀ {Γ Δ A} → 𝔗𝔪 Γ Δ → 𝔗𝔪 (Γ · A) Δ
  -- products
  fst   : ∀ {Γ A B} → 𝔗𝔪 Γ (A ⊗ B) → 𝔗𝔪 Γ A
  snd   : ∀ {Γ A B} → 𝔗𝔪 Γ (A ⊗ B) → 𝔗𝔪 Γ B
  ⦅_,_⦆  : ∀ {Γ A B} → 𝔗𝔪 Γ A → 𝔗𝔪 Γ B → 𝔗𝔪 Γ (A ⊗ B)
  -- exponentials
  Λ     : ∀ {Γ A B} → 𝔗𝔪 (Γ · A) B → 𝔗𝔪 Γ (A ⇒ B)
  _⦅_⦆   : ∀ {Γ A B} → 𝔗𝔪 Γ (A ⇒ B) → 𝔗𝔪 Γ A → 𝔗𝔪 Γ B
  -- literals
  𝓁     : ∀ {Γ A} → 𝓐⟦ A ⟧ᵀ → 𝔗𝔪 Γ A

𝓐⟦_⟧ : ∀ {Γ A} → 𝔗𝔪 Γ A → 𝓐⟦ Γ ⟧𝒞 → 𝓐⟦ A ⟧ᵀ
𝓐⟦ 𝓏           ⟧ ⟨ _ ∷ a ⟩ = a
𝓐⟦ π t         ⟧ ⟨ θ ∷ _ ⟩ = 𝓐⟦ t ⟧ θ
𝓐⟦ fst t       ⟧ θ         = proj₁ (𝓐⟦ t ⟧ θ)
𝓐⟦ snd t       ⟧ θ         = proj₂ (𝓐⟦ t ⟧ θ)
𝓐⟦ ⦅ t₁ , t₂ ⦆ ⟧ θ         = 𝓐⟦ t₁ ⟧ θ , 𝓐⟦ t₂ ⟧ θ
𝓐⟦ Λ t         ⟧ θ         = λ x → 𝓐⟦ t ⟧ ⟨ θ ∷ x ⟩
𝓐⟦ f ⦅ x ⦆     ⟧ θ         = 𝓐⟦ f ⟧ θ (𝓐⟦ x ⟧ θ)
𝓐⟦ 𝓁 l         ⟧ θ         = l

+𝔗𝔪 : ∀ A → 𝒲+ (λ Γ → 𝔗𝔪 Γ A)
+𝔗𝔪 _ ϵ₀     t          = t
+𝔗𝔪 _ (ω₁ w) 𝓏          = π (+𝔗𝔪 _ w 𝓏)
+𝔗𝔪 _ (ω₂ w) 𝓏          = 𝓏
+𝔗𝔪 _ (ω₁ w) (π t)      = π (+𝔗𝔪 _ w (π t))
+𝔗𝔪 _ (ω₂ w) (π t)      = π (+𝔗𝔪 _ w t)
+𝔗𝔪 _ w      (fst t)    = fst (+𝔗𝔪 _ w t)
+𝔗𝔪 _ w      (snd t)    = snd (+𝔗𝔪 _ w t)
+𝔗𝔪 _ w      ⦅ t₁ , t₂ ⦆ = ⦅ +𝔗𝔪 _ w t₁ , +𝔗𝔪 _ w t₂ ⦆
+𝔗𝔪 _ w      (Λ t)      = Λ (+𝔗𝔪 _ (ω₂ w) t)
+𝔗𝔪 _ w      (f ⦅ x ⦆)  = +𝔗𝔪 _ w f ⦅ +𝔗𝔪 _ w x ⦆
+𝔗𝔪 _ w      (𝓁 l)      = 𝓁 l

+𝓐 : ∀ {Γ Δ} → 𝒲 Γ Δ → 𝓐⟦ Γ ⟧𝒞 → 𝓐⟦ Δ ⟧𝒞
+𝓐 ϵ₀     θ         = θ
+𝓐 (ω₁ w) ⟨ γ ∷ _ ⟩ = +𝓐 w γ
+𝓐 (ω₂ w) ⟨ γ ∷ a ⟩ = ⟨ +𝓐 w γ ∷ a ⟩
