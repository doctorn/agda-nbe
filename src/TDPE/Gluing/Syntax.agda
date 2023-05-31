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
    β : ∀ {f : 𝔗𝔪₀ (Γ · A) B} {x : 𝔗𝔪₀ Γ A} → Λ f ⦅ x ⦆ ↦₀ f [ id ∷ x ]
    η : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} → f ↦₀ Λ ((p f) ⦅ 𝓏 ⦆)
    𝓏 : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (𝓏 [ γ ∷ a ]) ↦₀ a
    p : ∀ {t : 𝔗𝔪₀ Γ B} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (p t) [ γ ∷ a ] ↦₀ t [ γ ]

    app-stepₗ : ∀ {f g : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → f ↦₀ g → f ⦅ x ⦆ ↦₀ g ⦅ x ⦆
    app-stepᵣ : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x y : 𝔗𝔪₀ Γ A} → x ↦₀ y → f ⦅ x ⦆ ↦₀ f ⦅ y ⦆
    Λ-step    : ∀ {f g : 𝔗𝔪₀ (Γ · A) B} → f ↦₀ g → Λ f ↦₀ Λ g
    sb-stepₗ  : ∀ {s t : 𝔗𝔪₀ Γ A} {γ : 𝔗𝔪 Δ Γ} → s ↦₀ t → s [ γ ] ↦₀ t [ γ ]
    sb-stepᵣ  : ∀ {t : 𝔗𝔪₀ Γ A} {γ δ : 𝔗𝔪 Δ Γ} → γ ↦ δ → t [ γ ] ↦₀ t [ δ ]

    sb-id    : ∀ {x : 𝔗𝔪₀ Γ A} → x [ id {Γ} ] ↦₀ x
    sb-app   : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → (f ⦅ x ⦆) [ γ ] ↦₀ (f [ γ ]) ⦅ x [ γ ] ⦆
    sb-lam   : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ (Γ · A) B} → (Λ f) [ γ ] ↦₀ Λ (f [ ↑[ γ ] ])
    sb-assoc : ∀ {δ : 𝔗𝔪 Δ Γ} {γ : 𝔗𝔪 Ξ Δ} {t : 𝔗𝔪₀ Γ A} → (t [ δ ]) [ γ ] ↦₀ t [ δ ∘ γ ]

  data _↦_ : 𝔗𝔪 Δ Γ → 𝔗𝔪 Δ Γ → Set a where
    !-η     : ∀ {γ : 𝔗𝔪 Γ 𝟙} → γ ↦ !
    ∷-stepₗ : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → γ ↦ δ → (γ ∷ a) ↦ (δ ∷ a)
    ∷-stepᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → a ↦₀ b → (γ ∷ a) ↦ (γ ∷ b)

-- equivalence on clone
module _ {Γ A} where
  module C = E (_↦₀_ {Γ} {A})

-- equivalence on substitutions
module _ {Δ Γ} where
  module S = E (_↦_ {Δ} {Γ})

∷-congᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → a C.≈ b → γ ∷ a S.≈ γ ∷ b
∷-congᵣ E.refl = S.refl
∷-congᵣ (E.step xs (E.fwd x)) = S.step (∷-congᵣ xs) (S.fwd (∷-stepᵣ x))
∷-congᵣ (E.step xs (E.bwd x)) = S.step (∷-congᵣ xs) (S.bwd (∷-stepᵣ x))

∷-congₗ : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → γ S.≈ δ → γ ∷ a S.≈ δ ∷ a
∷-congₗ E.refl = E.refl
∷-congₗ (E.step xs (E.fwd x)) = E.step (∷-congₗ xs) (E.fwd (∷-stepₗ x))
∷-congₗ (E.step xs (E.bwd x)) = E.step (∷-congₗ xs) (E.bwd (∷-stepₗ x))

∷-cong₂ : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → γ S.≈ δ → a C.≈ b → γ ∷ a S.≈ δ ∷ b
∷-cong₂ x y = S.trans (∷-congₗ x) (∷-congᵣ y)

π-ext : ∀ {Γ} {δ : 𝔗𝔪 Ξ Δ} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Ξ A} → π γ ∘ (δ ∷ a) S.≈ γ ∘ δ
π-ext {Γ = 𝟙}     {γ = !}     = S.refl
π-ext {Γ = Γ · B} {γ = γ ∷ b} = ∷-cong₂ π-ext (C.unit p)

∘-identityˡ : ∀ {Γ} {γ : 𝔗𝔪 Δ Γ} → id ∘ γ S.≈ γ
∘-identityˡ {Γ = 𝟙}     {γ = !} = S.refl
∘-identityˡ {Γ = Γ · A} {γ ∷ a} = ∷-cong₂ (S.trans π-ext ∘-identityˡ) (C.unit 𝓏)

∘-identityʳ : ∀ {Γ} {γ : 𝔗𝔪 Δ Γ} → γ ∘ id S.≈ γ
∘-identityʳ {Γ = 𝟙}     {γ = !}     = S.refl
∘-identityʳ {Γ = Γ · A} {γ = γ ∷ a} = ∷-cong₂ ∘-identityʳ (C.unit sb-id)

∘-identity² : ∀ {Γ} → id ∘ id S.≈ id {Γ}
∘-identity² {Γ = 𝟙}     = S.refl
∘-identity² {Γ = Γ · A} = ∷-cong₂ (S.trans π-ext ∘-identityˡ) (C.unit 𝓏)

∘-assoc : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {ζ : 𝔗𝔪 Ω Ξ}
          → (γ ∘ δ) ∘ ζ S.≈ γ ∘ (δ ∘ ζ)
∘-assoc {γ = !}     {δ} {ζ} = S.refl
∘-assoc {γ = γ ∷ x} {δ} {ζ} = ∷-cong₂ ∘-assoc (C.unit sb-assoc)

∘-sym-assoc : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {ζ : 𝔗𝔪 Ω Ξ}
              → γ ∘ (δ ∘ ζ) S.≈ (γ ∘ δ) ∘ ζ
∘-sym-assoc = S.sym ∘-assoc

∘-stepₗ : ∀ {γ γ' : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} → γ S.~ γ' → γ ∘ δ S.~ γ' ∘ δ
∘-stepₗ {Γ = 𝟙} {γ = !} _ = S.bwd !-η
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (S.fwd (∷-stepₗ x))
  with ∘-stepₗ (S.fwd x)
... | S.fwd x' = S.fwd (∷-stepₗ x')
... | S.bwd x' = S.bwd (∷-stepₗ x')
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (S.bwd (∷-stepₗ x))
  with ∘-stepₗ (S.bwd x)
... | S.fwd x' = S.fwd (∷-stepₗ x')
... | S.bwd x' = S.bwd (∷-stepₗ x')
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (S.fwd (∷-stepᵣ x)) = S.fwd (∷-stepᵣ (sb-stepₗ x))
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (S.bwd (∷-stepᵣ x)) = S.bwd (∷-stepᵣ (sb-stepₗ x))

∘-stepᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ} → δ S.~ δ' → γ ∘ δ S.≈ γ ∘ δ'
∘-stepᵣ {Γ = 𝟙} {γ = !} x = S.refl
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (S.fwd (∷-stepₗ x)) =
  ∷-cong₂ (∘-stepᵣ (S.fwd (∷-stepₗ x))) (C.unit (sb-stepᵣ (∷-stepₗ x)))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (S.fwd (∷-stepᵣ x)) =
  ∷-cong₂ (∘-stepᵣ (S.fwd (∷-stepᵣ x))) (C.unit (sb-stepᵣ (∷-stepᵣ x)))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (S.bwd (∷-stepₗ x)) =
  S.sym (∷-cong₂ (∘-stepᵣ (S.fwd (∷-stepₗ x))) (C.unit (sb-stepᵣ (∷-stepₗ x))))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (S.bwd (∷-stepᵣ x)) =
  S.sym (∷-cong₂ (∘-stepᵣ (S.fwd (∷-stepᵣ x))) (C.unit (sb-stepᵣ (∷-stepᵣ x))))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (S.fwd (!-η)) =
  ∷-cong₂ (∘-stepᵣ (S.fwd !-η)) (C.unit (sb-stepᵣ !-η))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (S.bwd (!-η)) =
  S.sym (∷-cong₂ (∘-stepᵣ (S.fwd (!-η))) (C.unit (sb-stepᵣ !-η)))

∘-congₗ : ∀ {γ γ' : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ}
          → γ S.≈ γ' → γ ∘ δ S.≈ γ' ∘ δ
∘-congₗ E.refl        = S.refl
∘-congₗ (E.step xs x) = S.step (∘-congₗ xs) (∘-stepₗ x)

∘-congᵣ : ∀ {γ : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ}
          → δ S.≈ δ' → γ ∘ δ S.≈ γ ∘ δ'
∘-congᵣ E.refl        = S.refl
∘-congᵣ (E.step xs x) = S.trans (∘-congᵣ xs) (∘-stepᵣ x)

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
