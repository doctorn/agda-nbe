{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module TDPE.Gluing.Categories.Category.ContextualCartesianClosed
  {o ℓ e} (𝒞 : Category o ℓ e) (𝒰 : Set o) where

open import Level

open import TDPE.Gluing.Categories.Category.ContextualCartesian 𝒞 using (ContextualCartesian)
open import TDPE.Gluing.Contexts 𝒰 using (𝒰ᵀ) renaming (_⇒_ to _^_)

open Category 𝒞

record ContextualCartesianClosed : Set (levelOfTerm 𝒞) where
  field
    cartesian : ContextualCartesian (𝒰ᵀ)

  open ContextualCartesian cartesian

  field
    Λ : ∀ {Γ A B} → Γ · A ⇒ [ B ] → Γ ⇒ [ A ^ B ]

    eval : ∀ {A B} → [ A ^ B ] · A ⇒ [ B ]

  ↑[_] : ∀ {Δ Γ A} → Δ ⇒ Γ → (Δ · A) ⇒ (Γ · A)
  ↑[ f ] = ⟨ f ∘ π , 𝓏 ⟩

  field
    β : ∀ {Γ A B} (f : Γ · A ⇒ [ B ])
        → eval ∘ ⟨ Λ f ∘ π , 𝓏 ⟩ ≈ f

    unique : ∀ {Γ A B} {g : (Γ · A) ⇒ [ B ]} {h : Γ ⇒ [ A ^ B ]}
             → eval ∘ ↑[ h ] ≈ g
             → h ≈ Λ g

  η : ∀ {Γ A B} (f : Γ ⇒ [ A ^ B ]) → f ≈ Λ (eval ∘ ↑[ f ])
  η f = unique Equiv.refl

  β′ : ∀ {Γ A B} (f : Γ · A ⇒ [ B ]) (x : Γ ⇒ [ A ])
       → eval ∘ ⟨ Λ f , x ⟩ ≈ f ∘ ⟨ id , x ⟩
  β′ f x =  begin
      eval ∘ ⟨ Λ f , x ⟩
    ≈⟨
      Equiv.sym (∘-resp-≈ʳ
        (Ext.⟨⟩-cong₂
          (Equiv.trans
            assoc
            (Equiv.trans (∘-resp-≈ʳ Ext.project₁) identityʳ)
          )
          Ext.project₂)
        )
    ⟩
      eval ∘ (⟨ (Λ f ∘ π) ∘ ⟨ id , x ⟩ , 𝓏 ∘ ⟨ id , x ⟩ ⟩)
    ≈⟨ Equiv.sym (∘-resp-≈ʳ Ext.∘-distribʳ-⟨⟩) ⟩
      eval ∘ (⟨ Λ f ∘ π , 𝓏 ⟩ ∘ ⟨ id , x ⟩)
    ≈⟨ sym-assoc ⟩
      (eval ∘ ⟨ Λ f ∘ π , 𝓏 ⟩) ∘ ⟨ id , x ⟩
    ≈⟨ ∘-resp-≈ˡ (β f) ⟩
      f ∘ ⟨ id , x ⟩
    ∎
    where open HomReasoning

  Λ-cong : ∀ {Γ A B} {f g : Γ · A ⇒ [ B ]} → f ≈ g → Λ f ≈ Λ g
  Λ-cong {f = f} {g} f≈g = unique (Equiv.trans (β f) f≈g)

  subst : ∀ {Δ Γ A B} (f : Γ · A ⇒ [ B ]) (γ : Δ ⇒ Γ)
          → Λ f ∘ γ ≈ Λ (f ∘ ↑[ γ ])
  subst f γ = unique (begin
      eval ∘ ⟨ (Λ f ∘ γ) ∘ π , 𝓏 ⟩
    ≈⟨
      Equiv.sym (∘-resp-≈ʳ (Ext.⟨⟩-cong₂
        (Equiv.trans assoc
                     (Equiv.trans (∘-resp-≈ʳ Ext.project₁) sym-assoc)) Ext.project₂)
      )
    ⟩
      eval ∘ ⟨ (Λ f ∘ π) ∘ ↑[ γ ] , 𝓏 ∘ ↑[ γ ] ⟩
    ≈⟨ Equiv.sym (∘-resp-≈ʳ Ext.∘-distribʳ-⟨⟩) ⟩
      eval ∘ ⟨ Λ f ∘ π , 𝓏 ⟩ ∘ ↑[ γ ]
    ≈⟨ sym-assoc ⟩
      (eval ∘ ⟨ Λ f ∘ π , 𝓏 ⟩) ∘ ↑[ γ ]
    ≈⟨ ∘-resp-≈ˡ (β f) ⟩
      f ∘ ↑[ γ ]
    ∎)
    where open HomReasoning
