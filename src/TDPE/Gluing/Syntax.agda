{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Syntax {a} (𝒰 : Set a) where

open import Level

open import TDPE.Gluing.Weakenings 𝒰 using (ℭ; _ᵀ; _·_; 𝟙; `_`; _⇒_)
import TDPE.Gluing.Util.Equivalence as E

open import Categories.Category using (Category)

infixl 8 _∷_
infixl 9 _∘_
infix 4 _↦₀_ _↦_

private
  variable
    Γ Δ Ξ Ω : ℭ
    A B : 𝒰 ᵀ

mutual
  data 𝔗𝔪₀ : ℭ → 𝒰 ᵀ → Set a where
    -- variables
    𝓏     : 𝔗𝔪₀ (Γ · A) A
    p     : 𝔗𝔪₀ Γ B → 𝔗𝔪₀ (Γ · A) B
    -- exponentials
    Λ     : 𝔗𝔪₀ (Γ · A) B → 𝔗𝔪₀ Γ (A ⇒ B)
    _⦅_⦆  : 𝔗𝔪₀ Γ (A ⇒ B) → 𝔗𝔪₀ Γ A → 𝔗𝔪₀ Γ B
    -- substitution
    _[_] : 𝔗𝔪₀ Γ A → 𝔗𝔪 Δ Γ → 𝔗𝔪₀ Δ A

  data 𝔗𝔪 : ℭ → ℭ → Set a where
    !   : 𝔗𝔪 Γ 𝟙
    _∷_ : 𝔗𝔪 Δ Γ → 𝔗𝔪₀ Δ A → 𝔗𝔪 Δ (Γ · A)

π : 𝔗𝔪 Δ Γ → 𝔗𝔪 (Δ · A) Γ
π !       = !
π (γ ∷ a) = π γ ∷ p a

-- syntactic substitution
_∘_ : 𝔗𝔪 Δ Γ → 𝔗𝔪 Ξ Δ → 𝔗𝔪 Ξ Γ
!       ∘ δ = !
(γ ∷ a) ∘ δ = (γ ∘ δ) ∷ (a [ δ ])

id : ∀ {Γ} → 𝔗𝔪 Γ Γ
id {𝟙}     = !
id {Γ · A} = π id ∷ 𝓏

-- de bruijin lifiting
↑[_] : 𝔗𝔪 Δ Γ → 𝔗𝔪 (Δ · A) (Γ · A)
↑[ γ ] = π γ ∷ 𝓏

-- singleton
⟨_⟩ : 𝔗𝔪₀ Γ A → 𝔗𝔪 Γ (𝟙 · A)
⟨_⟩ = ! ∷_

-- admissible definition of substitution
_∘'_ : 𝔗𝔪 Ξ Δ → 𝔗𝔪 Δ Γ → 𝔗𝔪 Ξ Γ
_[_]' : 𝔗𝔪₀ Γ A → 𝔗𝔪 Δ Γ → 𝔗𝔪₀ Δ A

δ ∘' !       = !
δ ∘' (γ ∷ a) = (δ ∘' γ) ∷ (a [ δ ]')

𝓏         [ γ ∷ a ]' = a
p t       [ γ ∷ _ ]' = t [ γ ]'
(f ⦅ x ⦆) [ γ     ]' = (f [ γ ]') ⦅ x [ γ ]' ⦆
Λ t       [ γ     ]' = Λ (t [ ↑[ γ ] ]')
(t [ γ ]) [ γ'    ]' = t [ γ' ∘' γ ]'

mutual
  data _↦₀_ : 𝔗𝔪₀ Γ A → 𝔗𝔪₀ Γ A → Set a where
    Λβ₀ : ∀ {f : 𝔗𝔪₀ (Γ · A) B} {x : 𝔗𝔪₀ Γ A} → Λ f ⦅ x ⦆ ↦₀ f [ id ∷ x ]
    Λη₀ : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} → f ↦₀ Λ ((p f) ⦅ 𝓏 ⦆)
    v𝓏₀ : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (𝓏 [ γ ∷ a ]) ↦₀ a
    vp₀ : ∀ {t : 𝔗𝔪₀ Γ B} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (p t) [ γ ∷ a ] ↦₀ t [ γ ]

    app-stepₗ : ∀ {f g : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → f ↦₀ g → f ⦅ x ⦆ ↦₀ g ⦅ x ⦆
    app-stepᵣ : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x y : 𝔗𝔪₀ Γ A} → x ↦₀ y → f ⦅ x ⦆ ↦₀ f ⦅ y ⦆
    Λ-step    : ∀ {f g : 𝔗𝔪₀ (Γ · A) B} → f ↦₀ g → Λ f ↦₀ Λ g
    sb-stepₗ  : ∀ {s t : 𝔗𝔪₀ Γ A} {γ : 𝔗𝔪 Δ Γ} → s ↦₀ t → s [ γ ] ↦₀ t [ γ ]
    sb-stepᵣ  : ∀ {t : 𝔗𝔪₀ Γ A} {γ δ : 𝔗𝔪 Δ Γ} → γ ↦ δ → t [ γ ] ↦₀ t [ δ ]

    sb-id₀    : ∀ {x : 𝔗𝔪₀ Γ A} → x [ id {Γ} ] ↦₀ x
    sb-app₀   : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → (f ⦅ x ⦆) [ γ ] ↦₀ (f [ γ ]) ⦅ x [ γ ] ⦆
    sb-lam₀   : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ (Γ · A) B} → (Λ f) [ γ ] ↦₀ Λ (f [ ↑[ γ ] ])
    sb-assoc₀ : ∀ {δ : 𝔗𝔪 Δ Γ} {γ : 𝔗𝔪 Ξ Δ} {t : 𝔗𝔪₀ Γ A} → (t [ δ ]) [ γ ] ↦₀ t [ δ ∘ γ ]

  data _↦_ : 𝔗𝔪 Δ Γ → 𝔗𝔪 Δ Γ → Set a where
    !η₀     : ∀ {γ : 𝔗𝔪 Γ 𝟙} → γ ↦ !
    ∷-stepₗ : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → γ ↦ δ → (γ ∷ a) ↦ (δ ∷ a)
    ∷-stepᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → a ↦₀ b → (γ ∷ a) ↦ (γ ∷ b)

-- equivalence on clone
module _ {Γ A} where
  module C = E (_↦₀_ {Γ} {A})

-- equivalence on substitutions
module _ {Δ Γ} where
  module S = E (_↦_ {Δ} {Γ})

project : {γ δ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → γ ∷ a S.≈ δ ∷ b → a C.≈ b
project = S.induct C.is-equiv P I
  where P : 𝔗𝔪 Δ (Γ · A) → 𝔗𝔪₀ Δ A
        P (_ ∷ a) = a

        I : {γ δ : 𝔗𝔪 Δ (Γ · A)} → γ ↦ δ → P γ C.≈ P δ
        I (∷-stepₗ x) = C.refl
        I (∷-stepᵣ x) = C.unit x

Λβ : ∀ {f : 𝔗𝔪₀ (Γ · A) B} {x : 𝔗𝔪₀ Γ A} → Λ f ⦅ x ⦆ C.≈ f [ id ∷ x ]
Λβ = C.unit Λβ₀

Λη : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} → f C.≈ Λ ((p f) ⦅ 𝓏 ⦆)
Λη = C.unit Λη₀

v𝓏 : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (𝓏 [ γ ∷ a ]) C.≈ a
v𝓏 = C.unit v𝓏₀

vp : ∀ {t : 𝔗𝔪₀ Γ B} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (p t) [ γ ∷ a ] C.≈ t [ γ ]
vp = C.unit vp₀

sb-id : ∀ {x : 𝔗𝔪₀ Γ A} → x [ id {Γ} ] C.≈ x
sb-id = C.unit sb-id₀

sb-app : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → (f ⦅ x ⦆) [ γ ] C.≈ (f [ γ ]) ⦅ x [ γ ] ⦆
sb-app = C.unit sb-app₀

sb-lam : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ (Γ · A) B} → (Λ f) [ γ ] C.≈ Λ (f [ ↑[ γ ] ])
sb-lam = C.unit sb-lam₀

sb-assoc : ∀ {δ : 𝔗𝔪 Δ Γ} {γ : 𝔗𝔪 Ξ Δ} {t : 𝔗𝔪₀ Γ A} → (t [ δ ]) [ γ ] C.≈ t [ δ ∘ γ ]
sb-assoc = C.unit sb-assoc₀

!η : ∀ {γ : 𝔗𝔪 Γ 𝟙} → γ S.≈ !
!η = S.unit !η₀

∷-congᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → a C.≈ b → γ ∷ a S.≈ γ ∷ b
∷-congᵣ = C.induct S.is-equiv (_ ∷_) (λ x → S.unit (∷-stepᵣ x))

∷-congₗ : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → γ S.≈ δ → γ ∷ a S.≈ δ ∷ a
∷-congₗ = S.induct S.is-equiv (_∷ _) λ x → S.unit (∷-stepₗ x)

∷-cong₂ : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → γ S.≈ δ → a C.≈ b → γ ∷ a S.≈ δ ∷ b
∷-cong₂ x y = S.trans (∷-congₗ x) (∷-congᵣ y)

πβ : ∀ {Γ} {δ : 𝔗𝔪 Ξ Δ} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Ξ A} → π γ ∘ (δ ∷ a) S.≈ γ ∘ δ
πβ {Γ = 𝟙}     {γ = !}     = S.refl
πβ {Γ = Γ · B} {γ = γ ∷ b} = ∷-cong₂ πβ vp

∘-identityˡ : ∀ {Γ} {γ : 𝔗𝔪 Δ Γ} → id ∘ γ S.≈ γ
∘-identityˡ {Γ = 𝟙}     {γ = !} = S.refl
∘-identityˡ {Γ = Γ · A} {γ ∷ a} = ∷-cong₂ (S.trans πβ ∘-identityˡ) v𝓏

∘-identityʳ : ∀ {Γ} {γ : 𝔗𝔪 Δ Γ} → γ ∘ id S.≈ γ
∘-identityʳ {Γ = 𝟙}     {γ = !}     = S.refl
∘-identityʳ {Γ = Γ · A} {γ = γ ∷ a} = ∷-cong₂ ∘-identityʳ sb-id

∘-identity² : ∀ {Γ} → id ∘ id S.≈ id {Γ}
∘-identity² {Γ = 𝟙}     = S.refl
∘-identity² {Γ = Γ · A} = ∷-cong₂ (S.trans πβ ∘-identityˡ) v𝓏

∘-assoc : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {ζ : 𝔗𝔪 Ω Ξ}
          → (γ ∘ δ) ∘ ζ S.≈ γ ∘ (δ ∘ ζ)
∘-assoc {γ = !}     {δ} {ζ} = S.refl
∘-assoc {γ = γ ∷ x} {δ} {ζ} = ∷-cong₂ ∘-assoc sb-assoc

∘-sym-assoc : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {ζ : 𝔗𝔪 Ω Ξ}
              → γ ∘ (δ ∘ ζ) S.≈ (γ ∘ δ) ∘ ζ
∘-sym-assoc = S.sym ∘-assoc

∘-stepₗ : ∀ {γ γ' : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} → γ ↦ γ' → γ ∘ δ S.≈ γ' ∘ δ
∘-stepₗ !η₀         = !η
∘-stepₗ (∷-stepₗ x) = ∷-congₗ (∘-stepₗ x)
∘-stepₗ (∷-stepᵣ x) = ∷-congᵣ (C.unit (sb-stepₗ x))

∘-stepᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ} → δ ↦ δ' → γ ∘ δ S.≈ γ ∘ δ'
∘-stepᵣ {γ = !}             _   = S.refl
∘-stepᵣ {γ = γ ∷ a} {δ = !} !η₀ = S.refl
∘-stepᵣ {γ = γ ∷ a}         q   = ∷-cong₂ (∘-stepᵣ q) (C.unit (sb-stepᵣ q))

∘-congₗ : ∀ {γ γ' : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ}
          → γ S.≈ γ' → γ ∘ δ S.≈ γ' ∘ δ
∘-congₗ = S.induct S.is-equiv (_∘ _) ∘-stepₗ

∘-congᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ}
          → δ S.≈ δ' → γ ∘ δ S.≈ γ ∘ δ'
∘-congᵣ = S.induct S.is-equiv (_ ∘_) ∘-stepᵣ

∘-resp-≈ : ∀ {Ξ Δ Γ} {γ γ' : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ}
           → γ S.≈ γ' → δ S.≈ δ' → γ ∘ δ S.≈ γ' ∘ δ'
∘-resp-≈ x y = S.trans (∘-congₗ x) (∘-congᵣ y)

𝕋𝕞 : Category a a a
𝕋𝕞 = record
  { Obj = ℭ
  ; _⇒_ = 𝔗𝔪
  ; _≈_ = S._≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = ∘-assoc
  ; sym-assoc = ∘-sym-assoc
  ; identityˡ = ∘-identityˡ
  ; identityʳ = ∘-identityʳ
  ; identity² = ∘-identity²
  ; equiv = S.is-equiv
  ; ∘-resp-≈ = ∘-resp-≈
  }

open import TDPE.Gluing.Categories.Category.ContextualCartesian 𝕋𝕞

𝕋𝕞-CC : ContextualCartesian (𝒰 ᵀ)
𝕋𝕞-CC = record
  { terminal = record
    { ⊤ = 𝟙
    ; ⊤-is-terminal = record
      { ! = !
      ; !-unique = λ f → S.sym !η
      }
    }
  ; _·_ = _·_
  ; π = π id
  ; 𝓏 = ! ∷ 𝓏
  ; extensions = record
    { ⟨_,_⟩ = λ γ a → γ ∷ (𝓏 [ a ])
    ; project₁ = S.trans πβ ∘-identityˡ
    ; project₂ = project₂
    ; unique = unique
    }
  }
  where project₂ : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Δ (𝟙 · A)} → (! ∷ 𝓏) ∘ (γ ∷ (𝓏 [ δ ])) S.≈ δ
        project₂ {δ = ! ∷ a} = ∷-congᵣ (C.trans v𝓏 v𝓏)

        unique : ∀ {δ : 𝔗𝔪 Δ (Γ · A)} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪 Δ (𝟙 · A)}
                 → π id ∘ δ S.≈ γ → ! ∷ (𝓏 [ δ ]) S.≈ a → γ ∷ (𝓏 [ a ]) S.≈ δ
        unique {δ = δ ∷ b} {a = ! ∷ a} p₁ p₂ =
          ∷-cong₂ (S.trans (S.sym p₁) (S.trans πβ ∘-identityˡ))
                  (C.trans v𝓏 (C.trans (C.sym (project p₂)) v𝓏))
