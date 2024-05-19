{-# OPTIONS --without-K --safe #-}

module NbE.Gluing.Representation {a} (𝒰 : Set a) where

open import Function.Equality

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import NbE.Gluing.Contexts 𝒰
open import NbE.Gluing.Weakenings 𝒰 using (𝕎; 𝒲; ω₁; ω₂; ϵ₀; ϵ)
import NbE.Gluing.Categories.Category.Instance.Presheaves 𝕎 as Psh

module 𝕎 = Category 𝕎

data var : ℭ → 𝒰ᵀ → Set a where
  𝓏 : ∀ {Γ A} → var (Γ · A) A
  π : ∀ {Γ A B} → var Γ A → var (Γ · B) A

-- neutrals & normals
mutual
  data ne₀ : ℭ → 𝒰ᵀ → Set a where
    𝓋    : ∀ {Γ A} → var Γ A → ne₀ Γ A
    _⦅_⦆ : ∀ {Γ A B} → ne₀ Γ (A ⇒ B) → nf₀ Γ A → ne₀ Γ B

  data nf₀ : ℭ → 𝒰ᵀ → Set a where
    ι : ∀ {Γ A} → ne₀ Γ ` A ` → nf₀ Γ ` A `
    Λ : ∀ {Γ A B} → nf₀ (Γ · A) B → nf₀ Γ (A ⇒ B)

+var : ∀ {A Γ Δ} → 𝒲 Δ Γ → var Γ A → var Δ A
+var (ω₁ w) x     = π (+var w x)
+var (ω₂ w) 𝓏     = 𝓏
+var (ω₂ w) (π x) = π (+var w x)

+ : ∀ {A Γ Δ} → 𝒲 Δ Γ → nf₀ Γ A → nf₀ Δ A
+′ : ∀ {A Γ Δ} → 𝒲 Δ Γ → ne₀ Γ A → ne₀ Δ A

+ w (ι t) = ι (+′ w t)
+ w (Λ t) = Λ (+ (ω₂ w) t)

+′ w (𝓋 x)    = 𝓋 (+var w x)
+′ w (t ⦅ x ⦆) = +′ w t ⦅ + w x ⦆

+var-identity : ∀ {Γ A} {x : var Γ A} → +var (𝕎.id {Γ}) x ≡ x
+var-identity {Γ = Γ · B} {x = 𝓏}   = PE.refl
+var-identity {Γ = Γ · B} {x = π x} = PE.cong π +var-identity

+var-homomorphism : ∀ {Ξ Δ Γ} {w₂ : 𝒲 Δ Ξ} {w₁ : 𝒲 Γ Δ}
                    → ∀ {A} {x : var Ξ A} → +var (w₂ 𝕎.∘ w₁) x ≡ +var w₁ (+var w₂ x)
+var-homomorphism {w₂ = w₂}    {ϵ₀}    {x = x}   = I
  where I : ∀ {A} {x : var 𝟙 A} → x ≡ +var ϵ₀ x
        I {x = ()}
+var-homomorphism {w₂ = w₂}    {ω₁ w₁} {x = x}   = PE.cong π +var-homomorphism
+var-homomorphism {w₂ = ω₁ w₂} {ω₂ w₁} {x = x}   = PE.cong π +var-homomorphism
+var-homomorphism {w₂ = ω₂ w₂} {ω₂ w₁} {x = 𝓏}   = PE.refl
+var-homomorphism {w₂ = ω₂ w₂} {ω₂ w₁} {x = π x} = PE.cong π +var-homomorphism

+-identity : ∀ {Γ A} {t : nf₀ Γ A} → + (𝕎.id {Γ}) t ≡ t
+′-identity : ∀ {Γ A} {t : ne₀ Γ A} → +′ (𝕎.id {Γ}) t ≡ t

+-identity {t = ι x} = PE.cong ι +′-identity
+-identity {t = Λ t} = PE.cong Λ +-identity

+′-identity {t = 𝓋 x}     = PE.cong 𝓋 +var-identity
+′-identity {t = t ⦅ x ⦆} = PE.cong₂ _⦅_⦆ +′-identity +-identity

+-homomorphism : ∀ {Ξ Δ Γ} {w₂ : 𝒲 Δ Ξ} {w₁ : 𝒲 Γ Δ}
                 → ∀ {A} {x y : nf₀ Ξ A} → x ≡ y → + (w₂ 𝕎.∘ w₁) x ≡ + w₁ (+ w₂ y)
+′-homomorphism : ∀ {Ξ Δ Γ} {w₂ : 𝒲 Δ Ξ} {w₁ : 𝒲 Γ Δ}
                  → ∀ {A} {x y : ne₀ Ξ A} → x ≡ y → +′ (w₂ 𝕎.∘ w₁) x ≡ +′ w₁ (+′ w₂ y)

+-homomorphism {x = ι x} PE.refl = PE.cong ι (+′-homomorphism PE.refl)
+-homomorphism {x = Λ x} PE.refl = PE.cong Λ (+-homomorphism PE.refl)

+′-homomorphism {x = 𝓋 x}    PE.refl = PE.cong 𝓋 +var-homomorphism
+′-homomorphism {x = t ⦅ x ⦆} PE.refl =
  PE.cong₂ _⦅_⦆ (+′-homomorphism PE.refl) (+-homomorphism PE.refl)

𝔑𝔣₀ : 𝒰ᵀ → Psh.Obj
𝔑𝔣₀ A = record
  { F₀ = λ Γ → PE.setoid (nf₀ Γ A)
  ; F₁ = λ w → record
    { _⟨$⟩_ = + w
    ; cong = PE.cong (+ w)
    }
  ; identity = λ x → PE.trans +-identity x
  ; homomorphism = λ {_} {_} {_} {f} {g} → +-homomorphism {w₂ = f} {w₁ = g}
  ; F-resp-≈ = λ f≈g x≈y → PE.cong₂ + f≈g x≈y
  }

𝔑𝔢₀ : 𝒰ᵀ → Psh.Obj
𝔑𝔢₀ A = record
  { F₀ = λ Γ → PE.setoid (ne₀ Γ A)
  ; F₁ = λ w → record
    { _⟨$⟩_ = +′ w
    ; cong = PE.cong (+′ w)
    }
  ; identity = λ x → PE.trans +′-identity x
  ; homomorphism = λ {_} {_} {_} {f} {g} → +′-homomorphism {w₂ = f} {w₁ = g}
  ; F-resp-≈ = λ f≈g x≈y → PE.cong₂ +′ f≈g x≈y
  }

module _ (𝒪 : 𝒰ᵀ → Psh.Obj) where
  infixl 6 _∷_
  infix 5 _≈_

  data Ext : ℭ → ℭ → Set a where
    !   : ∀ {Γ} → Ext Γ 𝟙
    _∷_ : ∀ {Δ Γ A} → Ext Δ Γ → Setoid.Carrier (Functor.₀ (𝒪 A) Δ) → Ext Δ (Γ · A)

  data _≈_ : ∀ {Δ Γ} → Ext Δ Γ → Ext Δ Γ → Set a where
    !   : ∀ {Γ} → ! {Γ} ≈ !
    _∷_ : ∀ {Δ Γ A} {γ δ : Ext Δ Γ} {a b : Setoid.Carrier (Functor.₀ (𝒪 A) Δ)}
          → γ ≈ δ → Setoid._≈_ (Functor.₀ (𝒪 A) Δ) a b → γ ∷ a ≈ δ ∷ b

  refl : ∀ {Δ Γ} {x : Ext Δ Γ} → x ≈ x
  refl {x = !}     = !
  refl {x = γ ∷ a} = refl ∷ Setoid.refl (Functor.₀ (𝒪 _) _)

  sym : ∀ {Δ Γ} {x y : Ext Δ Γ} → x ≈ y → y ≈ x
  sym !       = !
  sym (γ ∷ a) = sym γ ∷ Setoid.sym (Functor.₀ (𝒪 _) _) a

  trans : ∀ {Δ Γ} {x y z : Ext Δ Γ} → x ≈ y → y ≈ z → x ≈ z
  trans !       !       = !
  trans (γ ∷ a) (δ ∷ b) = trans γ δ ∷ Setoid.trans (Functor.₀ (𝒪 _) _) a b

  isEquivalence : ∀ {Δ Γ} → IsEquivalence (_≈_ {Δ} {Γ})
  isEquivalence = record
    { refl = refl ; sym = sym ; trans = trans }

  ext : ∀ {Δ Γ Ξ} → 𝒲 Δ Γ → Ext Γ Ξ → Ext Δ Ξ
  ext w !       = !
  ext w (γ ∷ a) = (ext w γ) ∷ (Functor.₁ (𝒪 _) w ⟨$⟩ a)

  ext-cong : ∀ {Δ Γ Ξ} {w : 𝒲 Δ Γ} {γ δ : Ext Γ Ξ} → γ ≈ δ → ext w γ ≈ ext w δ
  ext-cong ! = !
  ext-cong {w = w} (γ ∷ a) = (ext-cong γ) ∷ cong (Functor.₁ (𝒪 _) w) a

  ext-identity : ∀ {Δ Γ} {γ δ : Ext Δ Γ} → γ ≈ δ → ext 𝕎.id γ ≈ δ
  ext-identity ! = !
  ext-identity (γ ∷ a) = (ext-identity γ) ∷ Functor.identity (𝒪 _) a

  ext-homomorphism : ∀ {Δ Γ Ξ Ω} {w₂ : 𝒲 Ξ Δ} {w₁ : 𝒲 Ω Ξ} {γ δ : Ext Δ Γ}
                     → γ ≈ δ → ext (w₂ 𝕎.∘ w₁) γ ≈ ext w₁ (ext w₂ δ)
  ext-homomorphism ! = !
  ext-homomorphism (γ ∷ a) = (ext-homomorphism γ) ∷ (Functor.homomorphism (𝒪 _) a)

  ⟨_⟩ : ℭ → Psh.Obj
  ⟨_⟩ Δ = record
    { F₀ = λ Γ → record
      { Carrier = Ext Γ Δ
      ; _≈_ = _≈_ {Γ} {Δ}
      ; isEquivalence = isEquivalence
      }
    ; F₁ = λ f → record
      { _⟨$⟩_ = ext f
      ; cong = ext-cong
      }
    ; identity = ext-identity
    ; homomorphism = ext-homomorphism
    ; F-resp-≈ = λ f≈g x≈y →
      trans (ext-cong x≈y)
            (IsEquivalence.reflexive isEquivalence (PE.cong₂ ext f≈g PE.refl))
    }

  proj : ∀ {Δ A} → ⟨_⟩ (Δ · A) Psh.⇒ ⟨_⟩ Δ
  proj = ntHelper (record
    { η = λ Γ → record
      { _⟨$⟩_ = λ { (γ ∷ _) → γ }
      ; cong = λ { (γ ∷ _) → γ }
      }
    ; commute = λ f → λ { (γ ∷ _) → ext-cong γ }
    })

  zero : ∀ {Δ A} → ⟨_⟩ (Δ · A) Psh.⇒ ⟨_⟩ (𝟙 · A)
  zero = ntHelper (record
    { η = λ Γ → record
      { _⟨$⟩_ = λ { (_ ∷ a) → ! ∷ a }
      ; cong = λ { (_ ∷ a) → ! ∷ a }
      }
    ; commute = λ f → λ { (_ ∷ a) → ! ∷ cong (Functor.₁ (𝒪 _) f) a }
    })

  unit : ∀ {A} → 𝒪 A Psh.⇒ ⟨_⟩ (𝟙 · A)
  unit = ntHelper (record
    { η = λ Γ → record
      { _⟨$⟩_ = λ x → ! ∷ x
      ; cong = λ x → ! ∷ x
      }
    ; commute = λ f x → ! ∷ (cong (Functor.₁ (𝒪 _) f) x)
    })

  counit : ∀ {A} → ⟨_⟩ (𝟙 · A) Psh.⇒ 𝒪 A
  counit = ntHelper (record
    { η = λ Γ → record
      { _⟨$⟩_ = λ { (! ∷ x) → x }
      ; cong = λ { (! ∷ x) → x }
      }
    ; commute = λ { f (! ∷ x) → cong (Functor.₁ (𝒪 _) f) x }
    })

  zero′ : ∀ {Δ A} → ⟨_⟩ (Δ · A) Psh.⇒ 𝒪 A
  zero′ = counit Psh.∘ zero

𝔑𝔣 : ℭ → Psh.Obj
𝔑𝔣 = ⟨ 𝔑𝔣₀ ⟩

𝔑𝔢 : ℭ → Psh.Obj
𝔑𝔢 = ⟨ 𝔑𝔢₀ ⟩

identity : ∀ Γ → Ext 𝔑𝔢₀ Γ Γ
identity 𝟙       = !
identity (Γ · A) = ext 𝔑𝔢₀ (ω₁ ϵ) (identity Γ) ∷ 𝓋 𝓏
