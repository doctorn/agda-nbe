{-# OPTIONS --without-K --safe #-}

module TDPE.Gluing.Syntax {a} (𝒰 : Set a) where

open import Level

open import TDPE.Gluing.Contexts 𝒰
import TDPE.Gluing.Util.Equivalence as E

open import Categories.Category using (Category)

infixl 8 _∷_
infixl 9 _∘_
infix 4 _↦₀_ _↦_

private
  variable
    Γ Δ Ξ Ω : ℭ
    A B C : 𝒰ᵀ

mutual
  data 𝔗𝔪₀ : ℭ → 𝒰ᵀ → Set a where
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

-- de bruijin lifiting
↑[_] : 𝔗𝔪 Δ Γ → 𝔗𝔪 (Δ · A) (Γ · A)
↑[ γ ] = π γ ∷ 𝓏

id : ∀ {Γ} → 𝔗𝔪 Γ Γ
id {𝟙}     = !
id {Γ · A} = ↑[ id ]

-- singleton
⟨_⟩ : 𝔗𝔪₀ Γ A → 𝔗𝔪 Γ (𝟙 · A)
⟨_⟩ = ! ∷_

mutual
  data _↦₀_ : 𝔗𝔪₀ Γ A → 𝔗𝔪₀ Γ A → Set a where
    Λβ₀ : ∀ {f : 𝔗𝔪₀ (Γ · A) B} {x : 𝔗𝔪₀ Γ A} → (Λ f) ⦅ x ⦆ ↦₀ f [ id ∷ x ]
    Λη₀ : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} → f ↦₀ Λ ((f [ π id ]) ⦅ 𝓏 ⦆)
    v𝓏₀ : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (𝓏 [ γ ∷ a ]) ↦₀ a
    vp₀ : ∀ {t : 𝔗𝔪₀ Γ B} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (p t) [ γ ∷ a ] ↦₀ t [ γ ]

    p-step : ∀ {s t : 𝔗𝔪₀ Γ B} {A} → s ↦₀ t → p {A = A} s ↦₀ p {A = A} t
    app-stepₗ : ∀ {f g : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → f ↦₀ g → f ⦅ x ⦆ ↦₀ g ⦅ x ⦆
    app-stepᵣ : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x y : 𝔗𝔪₀ Γ A} → x ↦₀ y → f ⦅ x ⦆ ↦₀ f ⦅ y ⦆
    Λ-step    : ∀ {f g : 𝔗𝔪₀ (Γ · A) B} → f ↦₀ g → Λ f ↦₀ Λ g
    sb-stepₗ  : ∀ {s t : 𝔗𝔪₀ Γ A} {γ : 𝔗𝔪 Δ Γ} → s ↦₀ t → s [ γ ] ↦₀ t [ γ ]
    sb-stepᵣ  : ∀ {t : 𝔗𝔪₀ Γ A} {γ δ : 𝔗𝔪 Δ Γ} → γ ↦ δ → t [ γ ] ↦₀ t [ δ ]

    p-π₀ : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ A} → p {A = B} (f [ γ ]) ↦₀ f [ π {A = B} γ ]

    sb-id₀    : ∀ {x : 𝔗𝔪₀ Γ A} → x [ id {Γ} ] ↦₀ x
    sb-app₀   : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → (f ⦅ x ⦆) [ γ ] ↦₀ (f [ γ ]) ⦅ x [ γ ] ⦆
    sb-lam₀   : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ (Γ · A) B} → (Λ f) [ γ ] ↦₀ Λ (f [ ↑[ γ ] ])
    sb-assoc₀ : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} {t : 𝔗𝔪₀ Γ A} → (t [ γ ]) [ δ ] ↦₀ t [ γ ∘ δ ]

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

𝒵 : 𝔗𝔪 Δ (Γ · A) → 𝔗𝔪₀ Δ A
𝒵 (_ ∷ a) = a

𝒵-cong : ∀ {Δ Γ A} {γ δ : 𝔗𝔪 Δ (Γ · A)} → γ S.≈ δ → 𝒵 γ C.≈ 𝒵 δ
𝒵-cong = S.induct C.is-equiv 𝒵 I
  where I : {γ δ : 𝔗𝔪 Δ (Γ · A)} → γ ↦ δ → 𝒵 γ C.≈ 𝒵 δ
        I (∷-stepₗ x) = C.refl
        I (∷-stepᵣ x) = C.unit x

Λβ : ∀ {f : 𝔗𝔪₀ (Γ · A) B} {x : 𝔗𝔪₀ Γ A} → (Λ f) ⦅ x ⦆ C.≈ f [ id ∷ x ]
Λβ = C.unit Λβ₀

Λη : ∀ {f : 𝔗𝔪₀ Γ (A ⇒ B)} → f C.≈ Λ ((f [ π id ]) ⦅ 𝓏 ⦆)
Λη = C.unit Λη₀

v𝓏 : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (𝓏 [ γ ∷ a ]) C.≈ a
v𝓏 = C.unit v𝓏₀

v𝒵 : ∀ {γ : 𝔗𝔪 Δ (Γ · A)} → (𝓏 [ γ ]) C.≈ 𝒵 γ
v𝒵 {γ = _ ∷ _} = C.unit v𝓏₀

𝒵η : ∀ {γ : 𝔗𝔪 Δ (𝟙 · A)} → ! ∷ 𝒵 γ S.≈ γ
𝒵η {γ = ! ∷ _} = S.refl

𝒵p : ∀ {γ : 𝔗𝔪 Δ (𝟙 · A)} → p {A = B} (𝒵 γ) C.≈ 𝓏 [ π γ ]
𝒵p {γ = ! ∷ _} = C.sym v𝓏

vp : ∀ {t : 𝔗𝔪₀ Γ B} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Δ A} → (p t) [ γ ∷ a ] C.≈ t [ γ ]
vp = C.unit vp₀

p-π : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ A} → p {A = B} (f [ γ ]) C.≈ f [ π {A = B} γ ]
p-π = C.unit p-π₀

sb-id : ∀ {x : 𝔗𝔪₀ Γ A} → x [ id {Γ} ] C.≈ x
sb-id = C.unit sb-id₀

sb-app : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ Γ (A ⇒ B)} {x : 𝔗𝔪₀ Γ A} → (f ⦅ x ⦆) [ γ ] C.≈ (f [ γ ]) ⦅ x [ γ ] ⦆
sb-app = C.unit sb-app₀

sb-lam : ∀ {γ : 𝔗𝔪 Δ Γ} {f : 𝔗𝔪₀ (Γ · A) B} → (Λ f) [ γ ] C.≈ Λ (f [ ↑[ γ ] ])
sb-lam = C.unit sb-lam₀

sb-comp : ∀ {γ : 𝔗𝔪 Δ (Γ · A)} {δ : 𝔗𝔪 Ξ Δ} → 𝒵 γ [ δ ] C.≈ 𝒵 (γ ∘ δ)
sb-comp {γ = _ ∷ _} = C.refl

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

𝓏η : ∀ {γ : 𝔗𝔪 Δ (𝟙 · A)} → ! ∷ 𝓏 [ γ ] S.≈ γ
𝓏η {γ = ! ∷ _} = ∷-congᵣ v𝓏

Λ-cong : ∀ {s t : 𝔗𝔪₀ (Δ · A) B} → s C.≈ t → Λ s C.≈ Λ t
Λ-cong = C.induct C.is-equiv Λ λ x → C.unit (Λ-step x)

app-congₗ : ∀ {f g : 𝔗𝔪₀ Δ (A ⇒ B)} {x : 𝔗𝔪₀ Δ A} → f C.≈ g → f ⦅ x ⦆ C.≈ g ⦅ x ⦆
app-congₗ = C.induct C.is-equiv (_⦅ _ ⦆) λ x → C.unit (app-stepₗ x)

app-congᵣ : ∀ {f : 𝔗𝔪₀ Δ (A ⇒ B)} {x y : 𝔗𝔪₀ Δ A} → x C.≈ y → f ⦅ x ⦆ C.≈ f ⦅ y ⦆
app-congᵣ = C.induct C.is-equiv (_ ⦅_⦆) λ x → C.unit (app-stepᵣ x)

app-cong₂ : ∀ {f g : 𝔗𝔪₀ Δ (A ⇒ B)} {x y : 𝔗𝔪₀ Δ A} → f C.≈ g → x C.≈ y → f ⦅ x ⦆ C.≈ g ⦅ y ⦆
app-cong₂ x y = C.trans (app-congₗ x) (app-congᵣ y)

sb-congₗ : ∀ {s t : 𝔗𝔪₀ Γ A} {γ : 𝔗𝔪 Δ Γ} → s C.≈ t → s [ γ ] C.≈ t [ γ ]
sb-congₗ = C.induct C.is-equiv (_[ _ ]) λ x → C.unit (sb-stepₗ x)

sb-congᵣ : ∀ {t : 𝔗𝔪₀ Γ A} {γ δ : 𝔗𝔪 Δ Γ} → γ S.≈ δ → t [ γ ] C.≈ t [ δ ]
sb-congᵣ = S.induct C.is-equiv (_ [_]) λ x → C.unit (sb-stepᵣ x)

sb-cong₂ : ∀ {s t : 𝔗𝔪₀ Γ A} {γ δ : 𝔗𝔪 Δ Γ} → s C.≈ t → γ S.≈ δ → s [ γ ] C.≈ t [ δ ]
sb-cong₂ x y = C.trans (sb-congₗ x) (sb-congᵣ y)

p-cong : ∀ {s t : 𝔗𝔪₀ Δ B} {A} → s C.≈ t → p {A = A} s C.≈ p {A = A} t
p-cong = C.induct C.is-equiv p λ x → C.unit (p-step x)

project : ∀ {γ δ : 𝔗𝔪 Δ Γ} {a b : 𝔗𝔪₀ Δ A} → γ ∷ a S.≈ δ ∷ b → γ S.≈ δ
project = S.induct S.is-equiv (λ { (γ ∷ _) → γ }) λ { (∷-stepₗ x) → S.unit x ; (∷-stepᵣ x) → S.refl }

πβ : ∀ {Γ} {δ : 𝔗𝔪 Ξ Δ} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪₀ Ξ A} → π γ ∘ (δ ∷ a) S.≈ γ ∘ δ
πβ {Γ = 𝟙}     {γ = !}     = S.refl
πβ {Γ = Γ · B} {γ = γ ∷ b} = ∷-cong₂ πβ vp

π-lemma : ∀ {γ : 𝔗𝔪 Δ Γ} {δ : 𝔗𝔪 Ξ Δ} → γ ∘ π δ S.≈ π {A = A} (γ ∘ δ)
π-lemma {γ = !}     = !η
π-lemma {γ = γ ∷ a} = ∷-cong₂ π-lemma (C.sym p-π)

π-cong : ∀ {γ δ : 𝔗𝔪 Δ Γ} → γ S.≈ δ → π γ S.≈ π {A = A} δ
π-cong {γ = !}     {δ = !}     _ = !η
π-cong {γ = γ ∷ x} {δ = δ ∷ y} q = ∷-cong₂ (π-cong (project q)) (p-cong (𝒵-cong q))

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

π-id : ∀ {γ : 𝔗𝔪 Δ Γ} → γ ∘ π id S.≈ π {A = A} γ
π-id = S.trans π-lemma (π-cong ∘-identityʳ)

πβ′ : ∀ {δ : 𝔗𝔪 Ξ Δ} {a : 𝔗𝔪₀ Ξ A} → π id ∘ (δ ∷ a) S.≈ δ
πβ′ = S.trans πβ ∘-identityˡ

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
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed 𝕋𝕞

CC : ContextualCartesian 𝒰ᵀ
CC = record
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
    { ⟨_,_⟩ = ⟨_,_⟩
    ; project₁ = project₁
    ; project₂ = project₂
    ; unique = unique
    }
  }
  where ⟨_,_⟩ : 𝔗𝔪 Δ Γ → 𝔗𝔪 Δ (𝟙 · A) → 𝔗𝔪 Δ (Γ · A)
        ⟨ γ , ! ∷ a ⟩ = γ ∷ a

        project₁ : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪 Δ (𝟙 · A)} → π id ∘ ⟨ γ , a ⟩ S.≈ γ
        project₁ {a = ! ∷ a} = S.trans πβ ∘-identityˡ

        project₂ : ∀ {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪 Δ (𝟙 · A)} → (! ∷ 𝓏) ∘ ⟨ γ , a ⟩ S.≈ a
        project₂ {a = ! ∷ a} = ∷-congᵣ v𝓏

        unique : ∀ {δ : 𝔗𝔪 Δ (Γ · A)} {γ : 𝔗𝔪 Δ Γ} {a : 𝔗𝔪 Δ (𝟙 · A)}
                 → π id ∘ δ S.≈ γ → ! ∷ 𝓏 [ δ ] S.≈ a → ⟨ γ , a ⟩ S.≈ δ
        unique {δ = δ ∷ b} {a = ! ∷ a} p₁ p₂ =
          ∷-cong₂ (S.trans (S.sym p₁) project₁)
                  (C.trans (C.sym (𝒵-cong p₂)) v𝓏)

CCC : ContextualCartesianClosed 𝒰
CCC = record
  { cartesian = CC
  ; Λ = λ t → ! ∷ Λ (𝒵 t)
  ; eval = eval
  ; β = β
  ; unique = unique
  }
  where open C.≈-Reasoning

        eval : 𝔗𝔪 (𝟙 · A ⇒ B · A) (𝟙 · B)
        eval = ! ∷ p 𝓏 ⦅ 𝓏 ⦆

        𝔼 : ∀ (f : 𝔗𝔪 (Δ · A) (𝟙 · B)) → 𝔗𝔪 (Δ · A) (𝟙 · A ⇒ B · A)
        𝔼 f = ! ∷ (Λ (𝒵 f) [ π id ]) ∷ 𝓏

        β : ∀ (f : 𝔗𝔪 (Δ · A) (𝟙 · B))
            → eval ∘ 𝔼 f S.≈ f
        β (! ∷ f) = ∷-congᵣ (begin
            p 𝓏 ⦅ 𝓏 ⦆ [ 𝔼 (! ∷ f) ]
          ≈⟨ sb-app ⟩
            (p 𝓏 [ 𝔼 (! ∷ f) ]) ⦅ 𝓏 [ 𝔼 (! ∷ f) ] ⦆
          ≈⟨ app-cong₂ (C.trans (C.trans vp v𝓏) sb-lam) v𝓏 ⟩
            Λ (f [ ↑[ π id ] ]) ⦅ 𝓏 ⦆
          ≈⟨ Λβ ⟩
            f [ ↑[ π id ] ] [ id ∷ 𝓏 ]
          ≈⟨ sb-assoc ⟩
            f [ π (π id) ∘ (↑[ id ] ∷ 𝓏) ∷ (𝓏 [ ↑[ id ] ∷ 𝓏 ]) ]
          ≈⟨ sb-congᵣ (∷-cong₂ (S.trans (S.trans πβ πβ) ∘-identityˡ) v𝓏) ⟩
            f [ id ]
          ≈⟨ sb-id ⟩
            f
          ∎)

        unique : ∀ {f : 𝔗𝔪 (Γ · A) (𝟙 · B)} {h : 𝔗𝔪 Γ (𝟙 · A ⇒ B)}
                 → eval ∘ (h ∘ π id ∷ 𝓏) S.≈ f
                 → h S.≈ ! ∷ Λ (𝒵 f)
        unique {f = ! ∷ f} {h = ! ∷ h} x = ∷-congᵣ (begin
            h
          ≈⟨ Λη ⟩
            Λ (h [ π id ] ⦅ 𝓏 ⦆)
          ≈⟨ C.sym(Λ-cong (C.trans sb-app (app-cong₂ (C.trans vp v𝓏) v𝓏))) ⟩
            Λ (p 𝓏 ⦅ 𝓏 ⦆ [ ! ∷ h [ π id ] ∷ 𝓏 ])
          ≈⟨ Λ-cong (𝒵-cong x) ⟩
            Λ f
          ∎)
