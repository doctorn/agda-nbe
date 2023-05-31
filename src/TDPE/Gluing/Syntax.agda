{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Syntax {a} (𝒰 : Set a) where

open import Level

open import TDPE.Gluing.Weakenings 𝒰 using (ℭ; _ᵀ; _·_; 𝟙; `_`; _⇒_)

open import Categories.Category using (Category)

infixl 8 _∷_
infixl 9 _∘_
infix 4 _↦₀_ _↦_ _~_ _≈_

mutual
  data 𝔗𝔪₀ : ℭ → 𝒰 ᵀ → Set a where
    -- variables
    𝓏     : ∀ {Γ A} → 𝔗𝔪₀ (Γ · A) A
    p     : ∀ {Γ A B} → 𝔗𝔪₀ Γ B → 𝔗𝔪₀ (Γ · A) B
    -- exponentials
    Λ     : ∀ {Γ A B} → 𝔗𝔪₀ (Γ · A) B → 𝔗𝔪₀ Γ (A ⇒ B)
    _⦅_⦆  : ∀ {Γ A B} → 𝔗𝔪₀ Γ (A ⇒ B) → 𝔗𝔪₀ Γ A → 𝔗𝔪₀ Γ B
    -- substitution
    _[_] : ∀ {Δ Γ A} → 𝔗𝔪₀ Γ A → 𝔗𝔪 Δ Γ → 𝔗𝔪₀ Δ A

  data 𝔗𝔪 : ℭ → ℭ → Set a where
    !   : ∀ {Γ} → 𝔗𝔪 Γ 𝟙
    _∷_ : ∀ {Δ Γ A} → 𝔗𝔪 Δ Γ → 𝔗𝔪₀ Δ A → 𝔗𝔪 Δ (Γ · A)

π : ∀ {Γ A Δ} → 𝔗𝔪 Δ Γ → 𝔗𝔪 (Δ · A) Γ
π !       = !
π (γ ∷ a) = π γ ∷ p a

-- syntactic substitution
_∘_ : ∀ {Γ Δ Ξ} → 𝔗𝔪 Δ Γ → 𝔗𝔪 Ξ Δ → 𝔗𝔪 Ξ Γ
!       ∘ δ = !
(γ ∷ a) ∘ δ = (γ ∘ δ) ∷ (a [ δ ])

id : ∀ {Γ} → 𝔗𝔪 Γ Γ
id {𝟙}     = !
id {Γ · A} = π id ∷ 𝓏

-- de bruijin lifiting
↑[_] : ∀ {Δ Γ A} → 𝔗𝔪 Δ Γ → 𝔗𝔪 (Δ · A) (Γ · A)
↑[ γ ] = π γ ∷ 𝓏

-- singleton
⟨_⟩ : ∀ {Γ A} → 𝔗𝔪₀ Γ A → 𝔗𝔪 Γ (𝟙 · A)
⟨_⟩ = ! ∷_

-- admissible definition of substitution
_∘'_ : ∀ {Γ Δ Ξ} → 𝔗𝔪 Ξ Δ → 𝔗𝔪 Δ Γ → 𝔗𝔪 Ξ Γ
_[_]' : ∀ {Δ Γ A} → 𝔗𝔪₀ Γ A → 𝔗𝔪 Δ Γ → 𝔗𝔪₀ Δ A

δ ∘' !       = !
δ ∘' (γ ∷ a) = (δ ∘' γ) ∷ (a [ δ ]')

𝓏         [ γ ∷ a ]' = a
p t       [ γ ∷ _ ]' = t [ γ ]'
(f ⦅ x ⦆) [ γ     ]' = (f [ γ ]') ⦅ x [ γ ]' ⦆
Λ t       [ γ     ]' = Λ (t [ ↑[ γ ] ]')
(t [ γ ]) [ γ' ]' = t [ γ' ∘' γ ]'

mutual
  data _↦₀_ : ∀ {Γ A} → 𝔗𝔪₀ Γ A → 𝔗𝔪₀ Γ A → Set a where
    β     : ∀ {Γ A B} (f : 𝔗𝔪₀ (Γ · A) B) (x : 𝔗𝔪₀ Γ A)  x → Λ f ⦅ x ⦆ ↦₀ f [ id ∷ x ]
    η     : ∀ {Γ A B} (f : 𝔗𝔪₀ Γ (A ⇒ B)) → f ↦₀ Λ ((p f) ⦅ 𝓏 ⦆)
    𝓏     : ∀ {Δ Γ A} (γ : 𝔗𝔪 Δ Γ) (a : 𝔗𝔪₀ Δ A) → (𝓏 [ γ ∷ a ]) ↦₀ a
    p     : ∀ {Δ Γ A B} (t : 𝔗𝔪₀ Γ B) (γ : 𝔗𝔪 Δ Γ) (a : 𝔗𝔪₀ Δ A) → (p t) [ γ ∷ a ] ↦₀ t [ γ ]

    _⦅_⦆ₗ : ∀ {Γ A B} {f g : 𝔗𝔪₀ Γ (A ⇒ B)} → f ↦₀ g → (x : 𝔗𝔪₀ Γ A) → f ⦅ x ⦆ ↦₀ g ⦅ x ⦆
    _⦅_⦆ᵣ : ∀ {Γ A B} (f : 𝔗𝔪₀ Γ (A ⇒ B)) {x y : 𝔗𝔪₀ Γ A} → x ↦₀ y → f ⦅ x ⦆ ↦₀ f ⦅ y ⦆
    Λ     : ∀ {Γ A B} {f g : 𝔗𝔪₀ (Γ · A) B} → f ↦₀ g → Λ f ↦₀ Λ g
    _[_]ₗ : ∀ {Δ Γ A} {s t : 𝔗𝔪₀ Γ A} → s ↦₀ t → (γ : 𝔗𝔪 Δ Γ) → s [ γ ] ↦₀ t [ γ ]
    _[_]ᵣ : ∀ {Δ Γ A} (t : 𝔗𝔪₀ Γ A) {γ δ : 𝔗𝔪 Δ Γ} → γ ↦ δ → t [ γ ] ↦₀ t [ δ ]

    sb-id : ∀ {Γ A} (x : 𝔗𝔪₀ Γ A) → x [ id {Γ} ] ↦₀ x
    sb-app : ∀ {Δ Γ A B} (γ : 𝔗𝔪 Δ Γ) (f : 𝔗𝔪₀ Γ (A ⇒ B)) (x : 𝔗𝔪₀ Γ A)
           → (f ⦅ x ⦆) [ γ ] ↦₀ (f [ γ ]) ⦅ x [ γ ] ⦆
    sb-lam : ∀ {Δ Γ A B} (γ : 𝔗𝔪 Δ Γ) (f : 𝔗𝔪₀ (Γ · A) B)
           → (Λ f) [ γ ] ↦₀ Λ (f [ ↑[ γ ] ])
    sb-assoc : ∀ {Γ Δ Ξ A} (δ : 𝔗𝔪 Δ Γ) (γ : 𝔗𝔪 Ξ Δ) (t : 𝔗𝔪₀ Γ A)
           → (t [ δ ]) [ γ ] ↦₀ t [ δ ∘ γ ]

  data _↦_ : ∀ {Δ Γ} → 𝔗𝔪 Δ Γ → 𝔗𝔪 Δ Γ → Set a where
    !    : ∀ {Γ} (γ : 𝔗𝔪 Γ 𝟙) → γ ↦ !
    _∷ₗ_ : ∀ {Δ Γ A} {γ δ : 𝔗𝔪 Δ Γ} → γ ↦ δ → (a : 𝔗𝔪₀ Δ A) → (γ ∷ a) ↦ (δ ∷ a)
    _∷ᵣ_ : ∀ {Δ Γ A} → (γ : 𝔗𝔪 Δ Γ) → {a b : 𝔗𝔪₀ Δ A} → a ↦₀ b → (γ ∷ a) ↦ (γ ∷ b)

data _~_ : ∀ {Δ Γ} → 𝔗𝔪 Δ Γ → 𝔗𝔪 Δ Γ → Set a where
  fwd : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Γ Δ} → γ ↦ δ → γ ~ δ
  bwd : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Γ Δ} → δ ↦ γ → γ ~ δ

data _≈_ :  ∀ {Δ Γ} → 𝔗𝔪 Δ Γ → 𝔗𝔪 Δ Γ → Set a where
  refl   : ∀ {Δ Γ} {γ : 𝔗𝔪 Δ Γ} → γ ≈ γ
  trans₀ : ∀ {Δ Γ} {ζ δ γ : 𝔗𝔪 Δ Γ} → ζ ≈ δ → δ ~ γ → ζ ≈ γ

unit : ∀ {Δ Γ} {δ γ : 𝔗𝔪 Δ Γ} → δ ↦ γ → δ ≈ γ
unit x = trans₀ refl (fwd x)

sym-unit : ∀ {Δ Γ} {δ γ : 𝔗𝔪 Δ Γ} → δ ↦ γ → γ ≈ δ
sym-unit x = trans₀ refl (bwd x)

trans : ∀ {Δ Γ} {ζ δ γ : 𝔗𝔪 Δ Γ} → ζ ≈ δ → δ ≈ γ → ζ ≈ γ
trans ys refl          = ys
trans ys (trans₀ xs x) = trans₀ (trans ys xs) x

flip : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Δ Γ} → γ ~ δ → δ ~ γ
flip (fwd x) = bwd x
flip (bwd x) = fwd x

-- TODO(@doctorn) optimise this
sym : ∀ {Δ Γ} {γ δ : 𝔗𝔪 Δ Γ} → γ ≈ δ → δ ≈ γ
sym refl                = refl
sym (trans₀ xs (fwd x)) = trans (sym-unit x) (sym xs)
sym (trans₀ xs (bwd x)) = trans (unit x) (sym xs)

∷-congᵣ : ∀ {Δ Γ A} {γ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A}
          → a ↦₀ b → γ ∷ a ≈ γ ∷ b
∷-congᵣ x = unit (_ ∷ᵣ x)

∷-congₗ : ∀ {Δ Γ A} {γ δ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A}
          → γ ≈ δ → γ ∷ a ≈ δ ∷ a
∷-congₗ refl = refl
∷-congₗ (trans₀ xs (fwd x)) = trans₀ (∷-congₗ xs) (fwd (x ∷ₗ _))
∷-congₗ (trans₀ xs (bwd x)) = trans₀ (∷-congₗ xs) (bwd (x ∷ₗ _))

∷-cong₂ : ∀ {Δ Γ A} {γ δ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A}
          → γ ≈ δ → a ↦₀ b → γ ∷ a ≈ δ ∷ b
∷-cong₂ x y = trans (∷-congₗ x) (∷-congᵣ y)

π-ext : ∀ {Ξ Δ Γ A} {δ : 𝔗𝔪 Ξ Δ} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Ξ A} → π γ ∘ (δ ∷ a) ≈ γ ∘ δ
π-ext {Γ = 𝟙} {γ = !} = refl
π-ext {Γ = Γ · B} {δ = δ} {γ ∷ b} {a} = ∷-cong₂ π-ext (p b δ a)

∘-identityˡ : ∀ {Δ Γ} {γ : 𝔗𝔪 Δ Γ} → id ∘ γ ≈ γ
∘-identityˡ {Γ = 𝟙}     {γ = !} = refl
∘-identityˡ {Γ = Γ · A} {γ ∷ a} = ∷-cong₂ (trans π-ext ∘-identityˡ) (𝓏 γ a)

∘-identityʳ : ∀ {Δ Γ} {γ : 𝔗𝔪 Δ Γ} → γ ∘ id ≈ γ
∘-identityʳ {Γ = 𝟙}     {γ = !}     = refl
∘-identityʳ {Γ = Γ · A} {γ = γ ∷ a} = ∷-cong₂ ∘-identityʳ (sb-id a)

∘-identity² : ∀ {Γ} → id ∘ id ≈ id {Γ}
∘-identity² {Γ = 𝟙}     = refl
∘-identity² {Γ = Γ · A} = ∷-cong₂ (trans π-ext ∘-identityˡ) (𝓏 (π id) 𝓏)

∘-assoc : ∀ {Ω Ξ Δ Γ} {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {ζ : 𝔗𝔪 Ω Ξ}
          → (γ ∘ δ) ∘ ζ ≈ γ ∘ (δ ∘ ζ)
∘-assoc {γ = !}     {δ} {ζ} = refl
∘-assoc {γ = γ ∷ x} {δ} {ζ} = ∷-cong₂ ∘-assoc (sb-assoc δ ζ x)

∘-sym-assoc : ∀ {Ω Ξ Δ Γ} {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {ζ : 𝔗𝔪 Ω Ξ}
              → γ ∘ (δ ∘ ζ) ≈ (γ ∘ δ) ∘ ζ
∘-sym-assoc = sym ∘-assoc

∘-stepₗ : ∀ {Ξ Δ Γ} {γ γ' : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ}
         → γ ~ γ' → γ ∘ δ ~ γ' ∘ δ
∘-stepₗ {Γ = 𝟙} {γ = !} x = bwd (! (_ ∘ _))
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (fwd (x ∷ₗ a))
  with ∘-stepₗ (fwd x)
... | fwd x' = fwd (x' ∷ₗ (a [ _ ]))
... | bwd x' = bwd (x' ∷ₗ (a [ _ ]))
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (bwd (x ∷ₗ a))
  with ∘-stepₗ (bwd x)
... | fwd x' = fwd (x' ∷ₗ (a [ _ ]))
... | bwd x' = bwd (x' ∷ₗ (a [ _ ]))
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (fwd (γ ∷ᵣ x)) = fwd ((γ ∘ _) ∷ᵣ (x [ _ ]ₗ))
∘-stepₗ {Γ = Γ · A} {γ = γ ∷ a} (bwd (γ ∷ᵣ x)) = bwd ((γ ∘ _) ∷ᵣ (x [ _ ]ₗ))

∘-stepᵣ : ∀ {Ξ Δ Γ} {γ : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ}
         → δ ~ δ' → γ ∘ δ ≈ γ ∘ δ'
∘-stepᵣ {Γ = 𝟙} {γ = !} x = refl
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (fwd (x ∷ₗ b)) = ∷-cong₂ (∘-stepᵣ (fwd (x ∷ₗ b))) (a [ x ∷ₗ b ]ᵣ)
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (fwd (δ ∷ᵣ x)) = ∷-cong₂ (∘-stepᵣ (fwd (δ ∷ᵣ x))) (a [ δ ∷ᵣ x ]ᵣ)
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (bwd (x ∷ₗ b)) = sym (∷-cong₂ (∘-stepᵣ (fwd (x ∷ₗ b))) (a [ x ∷ₗ b ]ᵣ))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (bwd (δ ∷ᵣ x)) = sym (∷-cong₂ (∘-stepᵣ (fwd (δ ∷ᵣ x))) (a [ δ ∷ᵣ x ]ᵣ))
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (fwd (! δ))    = ∷-cong₂ (∘-stepᵣ (fwd (! δ))) (a [ ! δ ]ᵣ)
∘-stepᵣ {Γ = Γ · A} {γ = γ ∷ a} (bwd (! δ))    = sym (∷-cong₂ (∘-stepᵣ (fwd (! δ))) (a [ ! δ ]ᵣ))

∘-congₗ : ∀ {Ξ Δ Γ} {γ γ' : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ}
           → γ ≈ γ' → γ ∘ δ ≈ γ' ∘ δ
∘-congₗ refl          = refl
∘-congₗ (trans₀ xs x) = trans₀ (∘-congₗ xs) (∘-stepₗ x)

∘-congᵣ : ∀ {Ξ Δ Γ} {γ : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ}
           → δ ≈ δ' → γ ∘ δ ≈ γ ∘ δ'
∘-congᵣ refl          = refl
∘-congᵣ (trans₀ xs x) = trans (∘-congᵣ xs) (∘-stepᵣ x)

∘-resp-≈ : ∀ {Ξ Δ Γ} {γ γ' : 𝔗𝔪 Δ Γ} {δ δ' : 𝔗𝔪 Ξ Δ}
           → γ ≈ γ' → δ ≈ δ' → γ ∘ δ ≈ γ' ∘ δ'
∘-resp-≈ x y = trans (∘-congₗ x) (∘-congᵣ y)

𝕋𝕞 : Category a a a
𝕋𝕞 = record
  { Obj = ℭ
  ; _⇒_ = 𝔗𝔪
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = ∘-assoc
  ; sym-assoc = ∘-sym-assoc
  ; identityˡ = ∘-identityˡ
  ; identityʳ = ∘-identityʳ
  ; identity² = ∘-identity²
  ; equiv = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
