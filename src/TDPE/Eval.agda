module TDPE.Eval where

open import TDPE.Base
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Function using () renaming (_∘_ to _$_)

-- closures
record 𝓛 (Γ : 𝒞) (A : 𝒰 ᵀ) : Set where
  constructor L
  field
    {Δ} : 𝒞
    f   : 𝓐⟦ Δ ⟧𝒞 → 𝓐⟦ A ⟧ᵀ
    w   : 𝒲 Γ Δ

  →𝔗𝔪 : 𝔗𝔪 Γ A
  →𝔗𝔪 = +𝔗𝔪 _ w (η Δ A f)
    where η : ∀ Δ A → (𝓐⟦ Δ ⟧𝒞 → 𝓐⟦ A ⟧ᵀ) → 𝔗𝔪 Δ A
          η 𝟙       A f = 𝓁 (f !)
          η (Δ · _) A f =
            +𝔗𝔪 _ (ω₁ ϵ) (η _ _ λ γ a → f ⟨ γ ∷ a ⟩) ⦅ 𝓏 ⦆

data 𝕍 : 𝒞 → 𝒰 ᵀ → Set where
  𝓏 : ∀ {Γ A} → 𝕍 (Γ · A) A
  π : ∀ {Γ A B} → 𝕍 Γ A → 𝕍 (Γ · B) A

-- neutrals & normals
mutual
  data 𝔑𝔢 : 𝒞 → 𝒰 ᵀ → Set where
    𝓋     : ∀ {Γ A} → 𝕍 Γ A → 𝔑𝔢 Γ A
    fst   : ∀ {Γ A B} → 𝔑𝔢 Γ (A ⊗ B) → 𝔑𝔢 Γ A
    snd   : ∀ {Γ A B} → 𝔑𝔢 Γ (A ⊗ B) → 𝔑𝔢 Γ B
    _⦅_⦆₁ : ∀ {Γ A B} → 𝔑𝔢 Γ (A ⇒ B) → 𝔑𝔣 Γ A → 𝔑𝔢 Γ B
    _⦅_⦆₂ : ∀ {Γ A B} → 𝓛 Γ (A ⇒ B) → 𝔑𝔢 Γ A → 𝔑𝔢 Γ B

  data 𝔑𝔣 : 𝒞 → 𝒰 ᵀ → Set where
    ι : ∀ {Γ A} → 𝔑𝔢 Γ ` A ` → 𝔑𝔣 Γ ` A `
    ⦅_,_⦆ : ∀ {Γ A B} → 𝔑𝔣 Γ A → 𝔑𝔣 Γ B → 𝔑𝔣 Γ (A ⊗ B)
    Λ : ∀ {Γ A B} → 𝔑𝔣 (Γ · A) B → 𝔑𝔣 Γ (A ⇒ B)
    𝓁 : ∀ {Γ A} → 𝓛 Γ A → 𝔑𝔣 Γ A

-- weakenings
+' : ∀ A → 𝒲+ (λ Γ → 𝔑𝔢 Γ A)
+ : ∀ A → 𝒲+ (λ Γ → 𝔑𝔣 Γ A)

+' _ ϵ₀ t          = t
+' _ w  (𝓋 x)      = 𝓋 (+𝕍 w x)
  where +𝕍 : ∀ {A} → 𝒲+ (λ Γ → 𝕍 Γ A)
        +𝕍 ϵ₀     x     = x
        +𝕍 (ω₁ w) x     = π (+𝕍 w x)
        +𝕍 (ω₂ w) 𝓏     = 𝓏
        +𝕍 (ω₂ w) (π x) = π (+𝕍 w x)
+' _ w  (fst x)    = fst (+' _ w x)
+' _ w  (snd x)    = snd (+' _ w x)
+' _ w  (f ⦅ x ⦆₁) = +' _ w f ⦅ + _ w x ⦆₁
+' _ w  (L f w' ⦅ x ⦆₂) = L f (w ∘ w') ⦅ +' _ w x ⦆₂

+ _ ϵ₀ t            = t
+ _ w  (ι x)        = ι (+' _ w x)
+ _ w  ⦅ t₁ , t₂ ⦆  = ⦅ + _ w t₁ , + _ w t₂ ⦆
+ _ w  (Λ t)        = Λ (+ _ (ω₂ w) t)
+ _ w  (𝓁 (L f w')) = 𝓁 (L f (w ∘ w'))

-- embeddings
𝒾 : ∀ {Γ A} → 𝔑𝔣 Γ A → 𝔗𝔪 Γ A
𝒾' : ∀ {Γ A} → 𝔑𝔢 Γ A → 𝔗𝔪 Γ A

𝒾 (ι x)        = 𝒾' x
𝒾 ⦅ t₁ , t₂ ⦆  = ⦅ 𝒾 t₁ , 𝒾 t₂ ⦆
𝒾 (Λ t)        = Λ (𝒾 t)
𝒾 (𝓁 l)        = 𝓛.→𝔗𝔪 l
𝒾' (𝓋 x)       = 𝒾𝓋 x
  where 𝒾𝓋 : ∀ {Γ A} → 𝕍 Γ A → 𝔗𝔪 Γ A
        𝒾𝓋 𝓏     = 𝓏
        𝒾𝓋 (π x) = π (𝒾𝓋 x)
𝒾' (fst t)    = fst (𝒾' t)
𝒾' (snd t)    = snd (𝒾' t)
𝒾' (f ⦅ x ⦆₁) = 𝒾' f ⦅ 𝒾 x ⦆
𝒾' (f ⦅ x ⦆₂) = 𝓛.→𝔗𝔪 f ⦅ 𝒾' x ⦆

-- relation
𝓡⟦_⟧ᵀ : 𝒰 ᵀ → 𝒞 → Set
𝓡⟦ τ ⟧ᵀ = ⟦ τ ⟧ᵀ (λ A Δ → 𝔑𝔣 Δ ` A `)
                 (λ P Q Δ → P Δ × Q Δ)
                 (λ P Q Δ → ∀ Γ → 𝒲 Γ Δ → P Γ → Q Γ)
𝓡⟦_⟧𝒞 : 𝒞 → 𝒞 → Set
𝓡⟦_⟧𝒞 Δ Γ = ⟨ (λ A → 𝓡⟦ A ⟧ᵀ Γ) ⟩ Δ

+𝓡 : ∀ A → 𝒲+ 𝓡⟦ A ⟧ᵀ
+𝓡 ` A `               = + ` A `
+𝓡 (A ⊗ B) w (η₁ , η₂) = +𝓡 A w η₁ , +𝓡 B w η₂
+𝓡 (A ⇒ B) w η Γ w'    = η Γ (w' ∘ w)

𝔮 : ∀ A Γ → 𝓡⟦ A ⟧ᵀ Γ → 𝔑𝔣 Γ A
𝔲 : ∀ A Γ → 𝔑𝔢 Γ A → 𝓡⟦ A ⟧ᵀ Γ

𝔮 ` A `   Δ x         = x
𝔮 (A ⊗ B) Δ (x₁ , x₂) = ⦅ 𝔮 A Δ x₁ , 𝔮 B Δ x₂ ⦆
𝔮 (A ⇒ B) Δ x         = Λ (𝔮 B (Δ · A) (x (Δ · A) (ω₁ ϵ) (𝔲 A (Δ · A) (𝓋 𝓏))))

𝔲 ` A `   Δ x       = ι x
𝔲 (A ⊗ B) Δ x       = 𝔲 A Δ (fst x) , 𝔲 B Δ (snd x)
𝔲 (A ⇒ B) Δ x Γ w y = 𝔲 B Γ (+' (A ⇒ B) w x ⦅ 𝔮 A Γ y ⦆₁)

↑ : ∀ A Γ → 𝓡⟦ A ⟧ᵀ Γ → 𝓐⟦ Γ ⟧𝒞 → 𝓐⟦ A ⟧ᵀ
↓ : ∀ A Γ → (𝓐⟦ Γ ⟧𝒞 → 𝓐⟦ A ⟧ᵀ) → ∀ Δ → 𝒲 Δ Γ → 𝓡⟦ A ⟧ᵀ Δ

↑ ` A ` Γ (ι x)       δ = 𝓐⟦ 𝒾' x ⟧ δ
↑ ` A ` Γ (𝓁 (L f w)) δ = f (+𝓐 w δ)
↑ (A ⊗ B) Γ (x₁ , x₂) δ = ↑ A Γ x₁ δ , ↑ B Γ x₂ δ
↑ (A ⇒ B) Γ f         δ = λ x → ↑ B (Γ · A) (f (Γ · A) (ω₁ ϵ) (↓ A (Γ · A) 𝓩 (Γ · A) ϵ)) ⟨ δ ∷ x ⟩

↓ ` A `   Γ x Δ w        = 𝓁 (L x w)
↓ (A ⊗ B) Γ x Δ w        = ↓ A Γ (proj₁ $ x) Δ w , ↓ B Γ (proj₂ $ x) Δ w
↓ (A ⇒ B) Γ f Δ w Ξ w' y = ↓ B Ξ (λ δ → f (+𝓐 (w' ∘ w) δ) (↑ A Ξ y δ)) Ξ ϵ

id : ∀ Γ → 𝓡⟦ Γ ⟧𝒞 Γ
id 𝟙       = !
id (Γ · A) = ⟨ ⟨+⟩ +𝓡 Γ (ω₁ ϵ) (id Γ) ∷ 𝔲 A (Γ · A) (𝓋 𝓏) ⟩

⟦_⟧ : ∀ {Γ A} → 𝔗𝔪 Γ A
     → ∀ Δ → 𝓡⟦ Γ ⟧𝒞 Δ → 𝓡⟦ A ⟧ᵀ Δ
⟦ 𝓏           ⟧ Δ ⟨ _ ∷ a ⟩ = a
⟦ π t         ⟧ Δ ⟨ γ ∷ _ ⟩ = ⟦ t ⟧ Δ γ
⟦ fst t       ⟧ Δ γ = proj₁ (⟦ t ⟧ Δ γ)
⟦ snd t       ⟧ Δ γ = proj₂ (⟦ t ⟧ Δ γ)
⟦ ⦅ t₁ , t₂ ⦆ ⟧ Δ γ = ⟦ t₁ ⟧ Δ γ , ⟦ t₂ ⟧ Δ γ
⟦ f ⦅ x ⦆     ⟧ Δ γ = ⟦ f ⟧ Δ γ Δ ϵ (⟦ x ⟧ Δ γ)
⟦ Λ t         ⟧ Δ γ Γ w x = ⟦ t ⟧ Γ ⟨ ⟨+⟩ +𝓡 _ w γ ∷ x ⟩
⟦_⟧ {A = A} (𝓁 l) Δ γ = ↓ A Δ (λ _ → l) Δ ϵ

nf : ∀ {Γ A} → 𝔗𝔪 Γ A → 𝔑𝔣 Γ A
nf {Γ} {A} t = 𝔮 A Γ (⟦ t ⟧ Γ (id Γ))

normalise : ∀ {Γ A} → 𝔗𝔪 Γ A → 𝔗𝔪 Γ A
normalise t = 𝒾 (nf t)
