{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

open import Level

module TDPE.Gluing.Interpretation
  {a} (𝒰 : Set a) {o ℓ e} (𝒞 : Category (a ⊔ o) ℓ e) where

open import Categories.Functor

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Syntax 𝒰 hiding (CC; CCC)

open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed

open import Relation.Binary using (IsEquivalence)

private
  variable
    Γ Δ Ξ Ω : ℭ
    A B : 𝒰ᵀ

module _ (CCC : ContextualCartesianClosed 𝒞 𝒰) where

  private
    module 𝒞 = Category 𝒞
    module 𝕋𝕞 = Category 𝕋𝕞

    module CCC = ContextualCartesianClosed CCC
    module CC = ContextualCartesian CCC.cartesian

    open Category 𝒞 hiding (_⇒_)
    open HomReasoning


    module _ {Δ Γ} where open IsEquivalence (𝒞.equiv {Δ} {Γ}) public

  ⟦_⟧₀ : ℭ → Obj
  ⟦ 𝟙     ⟧₀ = CC.Term.⊤
  ⟦ Γ · A ⟧₀ = ⟦ Γ ⟧₀ CC.· A

  ⟦_⟧C : 𝔗𝔪₀ Δ A → ⟦ Δ ⟧₀ 𝒞.⇒ ⟦ 𝟙 · A ⟧₀
  ⟦_⟧S : 𝔗𝔪 Δ Γ → ⟦ Δ ⟧₀ 𝒞.⇒ ⟦ Γ ⟧₀

  ⟦ 𝓏       ⟧C = CC.𝓏
  ⟦ p t     ⟧C = ⟦ t ⟧C 𝒞.∘ CC.π
  ⟦ Λ t     ⟧C = CCC.Λ ⟦ t ⟧C
  ⟦ f ⦅ x ⦆ ⟧C = CCC.eval 𝒞.∘ CC.⟨ ⟦ f ⟧C , ⟦ x ⟧C ⟩
  ⟦ t [ γ ] ⟧C = ⟦ t ⟧C 𝒞.∘ ⟦ γ ⟧S

  ⟦ !     ⟧S = CC.Term.!
  ⟦ γ ∷ a ⟧S = CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩

  ⟦_⟧-π-lemma : ∀ {γ : 𝔗𝔪 Δ Γ} → ⟦ π {A = A} γ ⟧S ≈ ⟦ γ ⟧S 𝒞.∘ CC.π
  ⟦_⟧-π-lemma {Δ = Δ} {γ = !} = CC.Term.!-unique (⟦ ! {Δ} ⟧S 𝒞.∘ CC.π)
  ⟦_⟧-π-lemma {γ = γ ∷ a} = CC.Ext.unique I II
    where I : CC.π 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ 𝒞.∘ CC.π ≈ ⟦ π γ ⟧S
          I = begin
              CC.π 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ 𝒞.∘ CC.π
            ≈⟨ sym-assoc ⟩
              (CC.π 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩) 𝒞.∘ CC.π
            ≈⟨ ∘-resp-≈ˡ CC.Ext.project₁ ⟩
              ⟦ γ ⟧S 𝒞.∘ CC.π
            ≈⟨ sym (⟦_⟧-π-lemma {γ = γ}) ⟩
              ⟦ π γ ⟧S
            ∎

          II : CC.𝓏 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ 𝒞.∘ CC.π ≈ ⟦ p a ⟧C
          II = begin
              CC.𝓏 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ 𝒞.∘ CC.π
            ≈⟨ sym-assoc ⟩
              (CC.𝓏 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩) 𝒞.∘ CC.π
            ≈⟨ ∘-resp-≈ˡ (CC.Ext.project₂) ⟩
              ⟦ a ⟧C 𝒞.∘ CC.π
            ∎

  ⟦_⟧-identity : ⟦ 𝕋𝕞.id {Γ} ⟧S ≈ 𝒞.id {⟦ Γ ⟧₀}
  ⟦_⟧-identity {Γ = 𝟙}     = CC.Term.!-unique 𝒞.id
  ⟦_⟧-identity {Γ = Γ · A} = begin
      CC.⟨ ⟦ π (𝕋𝕞.id {Γ}) ⟧S , CC.𝓏 ⟩
    ≈⟨ CC.Ext.⟨⟩-cong₂ (⟦_⟧-π-lemma {γ = 𝕋𝕞.id {Γ}}) refl ⟩
      CC.⟨ ⟦ 𝕋𝕞.id {Γ} ⟧S 𝒞.∘ CC.π  , CC.𝓏 ⟩
    ≈⟨ CC.Ext.⟨⟩-cong₂ (∘-resp-≈ˡ (⟦_⟧-identity {Γ})) refl ⟩
      CC.⟨ 𝒞.id 𝒞.∘ CC.π  , CC.𝓏 ⟩
    ≈⟨ CC.Ext.⟨⟩-cong₂ identityˡ refl ⟩
      CC.⟨ CC.π , CC.𝓏 ⟩
    ≈⟨ CC.Ext.η ⟩
      𝒞.id
    ∎

  ⟦_⟧-homomorphism : ∀ {δ : 𝔗𝔪 Ξ Δ} {γ : 𝔗𝔪 Δ Γ}
                     → ⟦ γ 𝕋𝕞.∘ δ ⟧S ≈ (⟦ γ ⟧S 𝒞.∘ ⟦ δ ⟧S)
  ⟦_⟧-homomorphism {Δ = Δ} {δ = δ} {γ = !} = CC.Term.!-unique (⟦ ! {Δ} ⟧S 𝒞.∘ ⟦ δ ⟧S)
  ⟦_⟧-homomorphism {δ = δ} {γ ∷ a} = CC.Ext.unique I II
    where I : CC.π 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ 𝒞.∘ ⟦ δ ⟧S ≈ ⟦ γ 𝕋𝕞.∘ δ ⟧S
          I = begin
              CC.π 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ 𝒞.∘ ⟦ δ ⟧S
            ≈⟨ sym-assoc ⟩
              (CC.π 𝒞.∘ CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩) 𝒞.∘ ⟦ δ ⟧S
            ≈⟨ ∘-resp-≈ˡ CC.Ext.project₁ ⟩
              ⟦ γ ⟧S 𝒞.∘ ⟦ δ ⟧S
            ≈⟨ sym (⟦_⟧-homomorphism {δ = δ} {γ}) ⟩
              ⟦ γ 𝕋𝕞.∘ δ ⟧S
            ∎

          II : CC.𝓏 𝒞.∘ ⟦ γ ∷ a ⟧S 𝒞.∘ ⟦ δ ⟧S ≈ ⟦ a [ δ ] ⟧C
          II = begin
              CC.𝓏 𝒞.∘ ⟦ γ ∷ a ⟧S 𝒞.∘ ⟦ δ ⟧S
            ≈⟨ sym-assoc ⟩
              (CC.𝓏 𝒞.∘ ⟦ γ ∷ a ⟧S) 𝒞.∘ ⟦ δ ⟧S
            ≈⟨ ∘-resp-≈ˡ CC.Ext.project₂ ⟩
              ⟦ a ⟧C 𝒞.∘ ⟦ δ ⟧S
            ∎

  ⟦_⟧-resp-≈ : ∀ {γ δ : 𝔗𝔪 Δ Γ} → γ S.≈ δ → ⟦ γ ⟧S ≈ ⟦ δ ⟧S
  ⟦_⟧-resp-≈ = S.induct 𝒞.equiv ⟦_⟧S I
    where I : ∀ {γ δ : 𝔗𝔪 Δ Γ} → γ ↦ δ → ⟦ γ ⟧S ≈ ⟦ δ ⟧S
          II : ∀ {γ δ : 𝔗𝔪₀ Δ A} → γ ↦₀ δ → ⟦ γ ⟧C ≈ ⟦ δ ⟧C

          I !η₀         = sym (CC.Term.!-unique _)
          I (∷-stepₗ x) = CC.Ext.⟨⟩-cong₂ (I x) refl
          I (∷-stepᵣ x) = CC.Ext.⟨⟩-cong₂ refl (II x)

          -- FIXME@(doctorn) why does it look like an SMT solver threw up on my code?
          II (Λβ₀ {Γ}) =
            trans (CCC.β′ _ _)
                  (∘-resp-≈ʳ (CC.Ext.⟨⟩-cong₂ (sym (⟦_⟧-identity {Γ})) refl))
          II {Δ} {A} Λη₀ =
            trans (CCC.η _)
                  (CCC.Λ-cong
                    (∘-resp-≈ʳ
                      (CC.Ext.⟨⟩-cong₂
                        (trans (∘-resp-≈ˡ (sym identityʳ))
                               (trans assoc
                                      (∘-resp-≈ʳ (trans (∘-resp-≈ˡ (sym (⟦_⟧-identity {Δ})))
                                                        (sym (⟦_⟧-π-lemma {γ = (𝕋𝕞.id {Δ})}))))))
                        refl)))
          II v𝓏₀ = CC.Ext.project₂
          II vp₀ = trans assoc (∘-resp-≈ʳ CC.Ext.project₁)
          II (p-step x)    = ∘-resp-≈ˡ (II x)
          II (app-stepₗ x) = ∘-resp-≈ʳ (CC.Ext.⟨⟩-cong₂ (II x) refl)
          II (app-stepᵣ x) = ∘-resp-≈ʳ (CC.Ext.⟨⟩-cong₂ refl (II x))
          II (Λ-step x)    = CCC.Λ-cong (II x)
          II (sb-stepₗ x)  = ∘-resp-≈ˡ (II x)
          II (sb-stepᵣ x)  = ∘-resp-≈ʳ (I x)
          II (sb-id₀ {Γ})  = trans (∘-resp-≈ʳ (⟦_⟧-identity {Γ})) identityʳ
          II sb-app₀       = trans assoc (∘-resp-≈ʳ CC.Ext.∘-distribʳ-⟨⟩)
          II (sb-lam₀ {γ = γ}) =
            trans (CCC.subst _ _)
                  (CCC.Λ-cong (∘-resp-≈ʳ (CC.Ext.⟨⟩-cong₂ (sym (⟦_⟧-π-lemma {γ = γ})) refl)))
          II (sb-assoc₀ {γ = γ} {δ}) =
            trans assoc (∘-resp-≈ʳ (sym (⟦_⟧-homomorphism {δ = δ} {γ})))
          II (p-π₀ {γ = γ} {f}) = trans assoc (∘-resp-≈ʳ (sym (⟦_⟧-π-lemma {γ = γ})))

  ⟦_⟧ : Functor 𝕋𝕞 𝒞
  ⟦_⟧ = record
    { F₀ = ⟦_⟧₀
    ; F₁ = ⟦_⟧S
    ; identity = λ {Γ} → ⟦_⟧-identity {Γ}
    ; homomorphism = λ {_} {_} {_} {f} {g} → ⟦_⟧-homomorphism {δ = f} {g}
    ; F-resp-≈ = ⟦_⟧-resp-≈
    }
