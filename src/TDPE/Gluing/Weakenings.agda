{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Weakenings {a} (𝒰 : Set a) where

open import Categories.Category using (Category)
open import Categories.Object.Terminal using (Terminal)

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

data _ᵀ {a} (𝒰 : Set a) : Set a where
  `_` : 𝒰 → 𝒰 ᵀ
  _⇒_ : 𝒰 ᵀ → 𝒰 ᵀ → 𝒰 ᵀ

infixl 5 _·_

data ℭ : Set a where
  𝟙 : ℭ
  _·_ : ℭ → 𝒰 ᵀ → ℭ

data 𝒲 : ℭ → ℭ → Set a where
  ϵ₀ : 𝒲 𝟙 𝟙
  ω₁ : ∀ {Γ Δ A} → 𝒲 Γ Δ → 𝒲 (Γ · A) Δ
  ω₂ : ∀ {Γ Δ A} → 𝒲 Γ Δ → 𝒲 (Γ · A) (Δ · A)

_∘_ : ∀ {Γ₁ Γ₂ Γ₃} → 𝒲 Γ₂ Γ₃ → 𝒲 Γ₁ Γ₂ → 𝒲 Γ₁ Γ₃
w'    ∘ ϵ₀   = w'
w'    ∘ ω₁ w = ω₁ (w' ∘ w)
ω₁ w' ∘ ω₂ w = ω₁ (w' ∘ w)
ω₂ w' ∘ ω₂ w = ω₂ (w' ∘ w)

ϵ : ∀ {Γ} → 𝒲 Γ Γ
ϵ {𝟙}     = ϵ₀
ϵ {_ · _} = ω₂ ϵ

! : ∀ {Γ} → 𝒲 Γ 𝟙
! {𝟙}     = ϵ₀
! {_ · _} = ω₁ !

!-unique : ∀ {Γ} (w : 𝒲 Γ 𝟙) → ! ≡ w
!-unique {𝟙}     ϵ₀     = PE.refl
!-unique {_ · _} (ω₁ w) = PE.cong ω₁ (!-unique w)

private
  variable
    Γ₁ Γ₂ Γ₃ Γ₄ : ℭ

∘-assoc : ∀ (w₁ : 𝒲 Γ₁ Γ₂) (w₂ : 𝒲 Γ₂ Γ₃) (w₃ : 𝒲 Γ₃ Γ₄)
          → (w₃ ∘ w₂) ∘ w₁ ≡ w₃ ∘ (w₂ ∘ w₁)
∘-assoc ϵ₀      w₂      w₃      = PE.refl
∘-assoc (ω₁ w₁) w₂      w₃      = PE.cong ω₁ (∘-assoc w₁ w₂ w₃)
∘-assoc (ω₂ w₁) (ω₁ w₂) w₃      = PE.cong ω₁ (∘-assoc w₁ w₂ w₃)
∘-assoc (ω₂ w₁) (ω₂ w₂) (ω₁ w₃) = PE.cong ω₁ (∘-assoc w₁ w₂ w₃)
∘-assoc (ω₂ w₁) (ω₂ w₂) (ω₂ w₃) = PE.cong ω₂ (∘-assoc w₁ w₂ w₃)

∘-sym-assoc : ∀ (w₁ : 𝒲 Γ₁ Γ₂) (w₂ : 𝒲 Γ₂ Γ₃) (w₃ : 𝒲 Γ₃ Γ₄)
              → w₃ ∘ (w₂ ∘ w₁) ≡ (w₃ ∘ w₂) ∘ w₁
∘-sym-assoc ϵ₀      w₂      w₃      = PE.refl
∘-sym-assoc (ω₁ w₁) w₂      w₃      = PE.cong ω₁ (∘-sym-assoc w₁ w₂ w₃)
∘-sym-assoc (ω₂ w₁) (ω₁ w₂) w₃      = PE.cong ω₁ (∘-sym-assoc w₁ w₂ w₃)
∘-sym-assoc (ω₂ w₁) (ω₂ w₂) (ω₁ w₃) = PE.cong ω₁ (∘-sym-assoc w₁ w₂ w₃)
∘-sym-assoc (ω₂ w₁) (ω₂ w₂) (ω₂ w₃) = PE.cong ω₂ (∘-sym-assoc w₁ w₂ w₃)

ϵ-identityˡ : ∀ (w : 𝒲 Γ₁ Γ₂) → ϵ ∘ w ≡ w
ϵ-identityˡ ϵ₀     = PE.refl
ϵ-identityˡ (ω₁ w) = PE.cong ω₁ (ϵ-identityˡ w)
ϵ-identityˡ (ω₂ w) = PE.cong ω₂ (ϵ-identityˡ w)

ϵ-identityʳ : ∀ {Γ₁} (w : 𝒲 Γ₁ Γ₂) → w ∘ ϵ  ≡ w
ϵ-identityʳ {Γ₁ = 𝟙}     w      = PE.refl
ϵ-identityʳ {Γ₁ = _ · _} (ω₁ w) = PE.cong ω₁ (ϵ-identityʳ w)
ϵ-identityʳ {Γ₁ = _ · _} (ω₂ w) = PE.cong ω₂ (ϵ-identityʳ w)

ϵ-identity² : ∀ {Γ} → ϵ ∘ ϵ ≡ ϵ {Γ}
ϵ-identity² {Γ = 𝟙}     = PE.refl
ϵ-identity² {Γ = _ · _} = PE.cong ω₂ ϵ-identity²

𝕎 : Category _ _ _
𝕎 = record
  { Obj = ℭ
  ; _⇒_ = 𝒲
  ; _≈_ = _≡_
  ; id = ϵ
  ; _∘_ = _∘_
  ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → ∘-assoc f g h
  ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} → ∘-sym-assoc f g h
  ; identityˡ = ϵ-identityˡ _
  ; identityʳ = ϵ-identityʳ _
  ; identity² = ϵ-identity²
  ; equiv = PE.isEquivalence
  ; ∘-resp-≈ = PE.cong₂ _∘_
  }

terminal : Terminal 𝕎
terminal = record
  { ⊤ = 𝟙
  ; ⊤-is-terminal = record
    { ! = !
    ; !-unique = !-unique
    }
  }

module _ {ℓ e} (𝒞 : Category a ℓ e) where

  open import Categories.Functor
  open import Categories.Functor.Properties using (Faithful)
  open import Categories.Object.Product 𝒞 using (IsProduct)
  open import TDPE.Gluing.Categories.Category.ContextualCartesian 𝒞

  module _ (CC : ContextualCartesian (𝒰 ᵀ)) where

    private
      module 𝒞 = Category 𝒞
      module 𝕎 = Category 𝕎
      module CC = ContextualCartesian CC
      open Category 𝒞
      open ContextualCartesian CC using (π; 𝓏; ⟨_,_⟩)
      open HomReasoning

    ⟦_⟧₀ : ℭ → 𝒞.Obj
    ⟦ 𝟙     ⟧₀ = Terminal.⊤ CC.terminal
    ⟦ Γ · A ⟧₀ = ⟦ Γ ⟧₀ CC.· A

    ⟦_⟧₁ : ∀ {Γ Δ} → 𝒲 Γ Δ → ⟦ Γ ⟧₀ 𝒞.⇒ ⟦ Δ ⟧₀
    ⟦ ϵ₀   ⟧₁ = 𝒞.id
    ⟦ ω₁ w ⟧₁ = ⟦ w ⟧₁ 𝒞.∘ π
    ⟦ ω₂ w ⟧₁ = ⟨ ⟦ ω₁ w ⟧₁ , 𝓏 ⟩

    ⟦_⟧-identity : ∀ {Γ} → ⟦ ϵ {Γ} ⟧₁ ≈ 𝒞.id {⟦ Γ ⟧₀}
    ⟦_⟧-identity {𝟙}     = Equiv.refl
    ⟦_⟧-identity {Γ · _} = IsProduct.unique CC.extensions I identityʳ
      where I : π 𝒞.∘ 𝒞.id ≈ ⟦ ϵ {Γ} ⟧₁ 𝒞.∘ π
            I = begin
                π 𝒞.∘ 𝒞.id
              ≈⟨ identityʳ ⟩
                π
              ≈⟨ Equiv.sym identityˡ ⟩
                𝒞.id 𝒞.∘ CC.π
              ≈⟨ ∘-resp-≈ˡ (Equiv.sym (⟦_⟧-identity {Γ})) ⟩
                ⟦ ϵ {Γ} ⟧₁ 𝒞.∘ π
              ∎

    ⟦_⟧-homomorphism : ∀ {w₁ : 𝒲 Γ₁ Γ₂} {w₂ : 𝒲 Γ₂ Γ₃}
                      → ⟦ w₂ 𝕎.∘ w₁ ⟧₁ ≈ ⟦ w₂ ⟧₁ 𝒞.∘ ⟦ w₁ ⟧₁
    ⟦_⟧-homomorphism {w₁ = ϵ₀}    {w₂} = Equiv.sym identityʳ
    ⟦_⟧-homomorphism {w₁ = ω₁ w₁} {w₂} = begin
        ⟦ w₂ 𝕎.∘ w₁ ⟧₁ 𝒞.∘ π
      ≈⟨ ∘-resp-≈ˡ (⟦_⟧-homomorphism {w₁ = w₁} {w₂}) ⟩
        (⟦ w₂ ⟧₁ 𝒞.∘ ⟦ w₁ ⟧₁) 𝒞.∘ π
      ≈⟨ assoc ⟩
        ⟦ w₂ ⟧₁ 𝒞.∘ ⟦ w₁ ⟧₁ 𝒞.∘ π
      ∎
    ⟦_⟧-homomorphism {w₁ = ω₂ w₁} {ω₁ w₂} = begin
        ⟦ w₂ 𝕎.∘ w₁ ⟧₁ 𝒞.∘ π
      ≈⟨ ∘-resp-≈ˡ (⟦_⟧-homomorphism {w₁ = w₁} {w₂}) ⟩
        (⟦ w₂ ⟧₁ 𝒞.∘ ⟦ w₁ ⟧₁) 𝒞.∘ π
      ≈⟨ assoc ⟩
        ⟦ w₂ ⟧₁ 𝒞.∘ (⟦ w₁ ⟧₁ 𝒞.∘ π)
      ≈⟨ ∘-resp-≈ʳ (Equiv.sym (IsProduct.project₁ CC.extensions)) ⟩
        ⟦ w₂ ⟧₁ 𝒞.∘ (π 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩)
      ≈⟨ sym-assoc ⟩
        (⟦ w₂ ⟧₁ 𝒞.∘ π) 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
      ∎
    ⟦_⟧-homomorphism {w₁ = ω₂ w₁} {ω₂ w₂} = IsProduct.unique CC.extensions I II
      where I = begin
                π 𝒞.∘ ⟨ ⟦ w₂ ⟧₁ 𝒞.∘ π , 𝓏 ⟩ 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
              ≈⟨ sym-assoc ⟩
                (π 𝒞.∘ ⟨ ⟦ w₂ ⟧₁ 𝒞.∘ π , 𝓏 ⟩) 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
              ≈⟨ ∘-resp-≈ˡ (IsProduct.project₁ CC.extensions) ⟩
                (⟦ w₂ ⟧₁ 𝒞.∘ π) 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
              ≈⟨ assoc ⟩
                ⟦ w₂ ⟧₁ 𝒞.∘ (π 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩)
              ≈⟨ ∘-resp-≈ʳ (IsProduct.project₁ CC.extensions) ⟩
                ⟦ w₂ ⟧₁ 𝒞.∘ (⟦ w₁ ⟧₁ 𝒞.∘ π)
              ≈⟨ sym-assoc ⟩
                (⟦ w₂ ⟧₁ 𝒞.∘ ⟦ w₁ ⟧₁) 𝒞.∘ π
              ≈⟨ ∘-resp-≈ˡ (Equiv.sym (⟦_⟧-homomorphism {w₁ = w₁} {w₂})) ⟩
                ⟦ w₂ 𝕎.∘ w₁ ⟧₁ 𝒞.∘ π
              ∎

            II = begin
                𝓏 𝒞.∘ ⟨ ⟦ w₂ ⟧₁ 𝒞.∘ π , 𝓏 ⟩ 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
              ≈⟨ sym-assoc ⟩
                (𝓏 𝒞.∘ ⟨ ⟦ w₂ ⟧₁ 𝒞.∘ π , 𝓏 ⟩) 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
              ≈⟨ ∘-resp-≈ˡ (IsProduct.project₂ CC.extensions) ⟩
                𝓏 𝒞.∘ ⟨ ⟦ w₁ ⟧₁ 𝒞.∘ π , 𝓏 ⟩
              ≈⟨ IsProduct.project₂ CC.extensions ⟩
                𝓏
              ∎

    ⟦_⟧-resp-≈ : ∀ {w₁ w₂ : 𝒲 Γ₁ Γ₂} → w₁ ≡ w₂ → ⟦ w₁ ⟧₁ ≈ ⟦ w₂ ⟧₁
    ⟦_⟧-resp-≈ w₁≡w₂ = Equiv.reflexive (PE.cong ⟦_⟧₁ w₁≡w₂)

    ⟦_⟧ : Functor 𝕎 𝒞
    ⟦_⟧ = record
      { F₀ = ⟦_⟧₀
      ; F₁ = ⟦_⟧₁
      ; identity = λ {Γ} → ⟦_⟧-identity {Γ}
      ; homomorphism = λ {_} {_} {_} {f} {g} → ⟦_⟧-homomorphism {w₁ = f} {g}
      ; F-resp-≈ = ⟦_⟧-resp-≈
      }
