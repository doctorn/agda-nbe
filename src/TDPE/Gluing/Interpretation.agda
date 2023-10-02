{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

open import Level

module TDPE.Gluing.Interpretation
  {a} (𝒰 : Set a) {o ℓ e} (𝒞 : Category (a ⊔ o) ℓ e) where

open import Categories.Functor using (Functor)

open import TDPE.Gluing.Contexts 𝒰
open import TDPE.Gluing.Syntax 𝒰 as Syntax hiding (CC; CCC)

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

    open Category 𝒞 hiding (_⇒_; _∘_; id)
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

  ⟦_⟧C-resp-≈ : ∀ {γ δ : 𝔗𝔪₀ Γ A} → γ C.≈ δ → ⟦ γ ⟧C ≈ ⟦ δ ⟧C
  ⟦_⟧C-resp-≈ q = trans (sym CC.Ext.project₂) (trans (∘-resp-≈ʳ (⟦_⟧-resp-≈ (∷-congᵣ {γ = !} q))) CC.Ext.project₂)

  ⟦_⟧ : Functor 𝕋𝕞 𝒞
  ⟦_⟧ = record
    { F₀ = ⟦_⟧₀
    ; F₁ = ⟦_⟧S
    ; identity = λ {Γ} → ⟦_⟧-identity {Γ}
    ; homomorphism = λ {_} {_} {_} {f} {g} → ⟦_⟧-homomorphism {δ = f} {g}
    ; F-resp-≈ = ⟦_⟧-resp-≈
    }

  open import TDPE.Gluing.Categories.Functor.ContextualCartesian {𝒞 = 𝕋𝕞} {𝒟 = 𝒞}
  open import TDPE.Gluing.Categories.Functor.ContextualCartesianClosed {𝒞 = 𝕋𝕞} {𝒟 = 𝒞}
  open import Relation.Binary.PropositionalEquality as PE using (_≡_)

  ⟦_⟧-CC : CCFunctor 𝒰ᵀ Syntax.CC CCC.cartesian ⟦_⟧
  ⟦_⟧-CC = record
    { terminal-preserving = PE.refl
    ; ·-preserving = PE.refl
    ; π-preserving =
      λ {Γ} → trans (⟦_⟧-π-lemma {γ = Syntax.id {Γ}}) (trans (𝒞.∘-resp-≈ˡ (⟦_⟧-identity {Γ})) 𝒞.identityˡ)
    ; 𝓏-preserving =
      λ {Γ} {A} →
        CC.Ext.unique (sym (CC.!-unique _)) (trans (∘-resp-≈ˡ CC.𝓏-id) 𝒞.identityˡ)
    }

  ⟦_⟧-CCC : CCCFunctor 𝒰 Syntax.CCC CCC ⟦_⟧
  ⟦_⟧-CCC = record
    { cartesian = ⟦_⟧-CC
    ; Λ-preserving = Λ-preserving
    ; eval-preserving = eval-preserving
    }
    where Λ-preserving : (h : 𝔗𝔪 (Γ · A) (𝟙 · B)) → CC.⟨ CC.! , CCC.Λ ⟦ 𝒵 h ⟧C ⟩ ≈ CCC.Λ ⟦ h ⟧S
          Λ-preserving h = begin
              CC.⟨ CC.! , CCC.Λ ⟦ 𝒵 h ⟧C ⟩
            ≈⟨ CC.⟨!, CCC.Λ ⟦ 𝒵 h ⟧C ⟩-id ⟩
              CCC.Λ ⟦ 𝒵 h ⟧C
            ≈⟨ CCC.Λ-cong (⟦_⟧C-resp-≈ {γ = 𝒵 h} {δ = 𝓏 [ h ]} (C.sym v𝒵)) ⟩
              CCC.Λ ⟦ 𝓏 [ h ] ⟧C
            ≈⟨ CCC.Λ-cong (trans (𝒞.∘-resp-≈ˡ CC.𝓏-id) 𝒞.identityˡ) ⟩
              CCC.Λ ⟦ h ⟧S
            ∎

          eval-preserving : CC.⟨ CC.! , CCC.eval 𝒞.∘ CC.⟨ CC.𝓏 𝒞.∘ CC.π , CC.𝓏 ⟩ ⟩ ≈ CCC.eval {A} {B}
          eval-preserving = begin
              CC.⟨ CC.! , CCC.eval 𝒞.∘ CC.⟨ CC.𝓏 𝒞.∘ CC.π , CC.𝓏 ⟩ ⟩
            ≈⟨
              CC.Ext.⟨⟩-cong₂ refl
                (trans (𝒞.∘-resp-≈ʳ (CC.Ext.unique (trans 𝒞.identityʳ (trans (sym 𝒞.identityˡ) (𝒞.∘-resp-≈ˡ (sym CC.𝓏-id)))) 𝒞.identityʳ))
                𝒞.identityʳ)
            ⟩
              CC.⟨ CC.! , CCC.eval ⟩
            ≈⟨ CC.⟨!, CCC.eval ⟩-id ⟩
              CCC.eval
            ∎

  module _ {F : Functor 𝕋𝕞 𝒞} (F-CCC : CCCFunctor 𝒰 Syntax.CCC CCC F) where

    private
      module F = Functor F
      module F-CCC = CCCFunctor F-CCC

      I : F.₀ Γ ≡ ⟦ Γ ⟧₀
      I {𝟙}     = F-CCC.terminal-preserving
      I {Γ · A} = PE.trans F-CCC.·-preserving (PE.cong (CC._· A) I)

      open import TDPE.Gluing.Transport 𝒞

      ⟦_⟧C-universal : (γ : 𝔗𝔪₀ Γ A) → F.₁ (! ∷ γ) ≈ transport′ I I ⟦ γ ⟧C
      ⟦_⟧S-universal : (γ : 𝔗𝔪 Δ Γ) → F.₁ γ ≈ transport′ I I ⟦ γ ⟧S


      ⟦_⟧C-universal = {!!}

      ⟦ !     ⟧S-universal = flip-transport {p = I} {I} (F.₁ !) CC.! (sym (CC.!-unique _))
      ⟦_⟧S-universal {Δ} {Γ · A} (γ ∷ a) = begin
          F.₁ (γ ∷ a)
        ≈⟨ flip-transport {p = I} {I} (F.₁ (γ ∷ a)) CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩ (sym (CC.Ext.unique unique-π unique-𝓏)) ⟩
          transport′ I I (CC.⟨ ⟦ γ ⟧S , ⟦ a ⟧C ⟩)
        ∎
        where transport-π : ∀ {Γ Γ'} {A} (p : Γ ≡ Γ') → CC.π {Γ'} {A} ≡ transport (PE.cong (CC._· A) p) p CC.π
              transport-π PE.refl = PE.refl

              transport-𝓏 : ∀ {Γ Γ'} {A} (p : Γ ≡ Γ') → CC.𝓏 {Γ'} {A} ≡ transport (PE.cong (CC._· A) p) PE.refl CC.𝓏
              transport-𝓏 PE.refl = PE.refl

              unique-π : CC.π 𝒞.∘ transport I I (F.₁ (γ ∷ a)) ≈ ⟦ γ ⟧S
              unique-π = begin
                  CC.π 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (reflexive (transport-π I)) ⟩
                  transport (PE.cong (CC._· A) (I {Γ})) I CC.π 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (sym (transport-≈ {p = PE.cong (CC._· _) I} {I} (transport F-CCC.·-preserving PE.refl (F.₁ (π id))) CC.π (flip-transport′ (F.₁ (π id)) CC.π F-CCC.π-preserving))) ⟩
                  transport (PE.cong (CC._· A) (I {Γ})) I (transport F-CCC.·-preserving PE.refl (F.₁ (π id))) 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (reflexive (transport-trans {p₁ = F-CCC.·-preserving} {PE.cong (CC._· _) I} {PE.refl} {I} (F.₁ (π id)))) ⟩
                  transport I I (F.₁ (π id)) 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≡⟨ transport-∘ (F.₁ (π id)) (F.₁ (γ ∷ a)) ⟩
                  transport I I (F.₁ (π id) 𝒞.∘ F.₁ (γ ∷ a))
                ≈⟨ transport-≈ (F.₁ (π id) 𝒞.∘ F.₁ (γ ∷ a)) (F.₁ (π id ∘ (γ ∷ a))) (sym F.homomorphism) ⟩
                  transport I I (F.₁ (π id ∘ (γ ∷ a)))
                ≈⟨ transport-≈ (F.₁ (π id ∘ (γ ∷ a))) (F.₁ γ) (F.F-resp-≈ πβ′) ⟩
                  transport I I (F.₁ γ)
                ≈⟨ flip-transport′ {p = I} {I} (F.₁ γ) ⟦ γ ⟧S (⟦ γ ⟧S-universal) ⟩
                  ⟦ γ ⟧S
                ∎

              unique-𝓏 : CC.𝓏 𝒞.∘ transport I I (F.₁ (γ ∷ a)) ≈ ⟦ a ⟧C
              unique-𝓏 = begin
                  CC.𝓏 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (reflexive (transport-𝓏 I)) ⟩
                  transport (PE.cong (CC._· A) (I {Γ})) PE.refl CC.𝓏 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (sym (transport-≈ {p = PE.cong (CC._· A) (I {Γ})} {PE.refl} (transport F-CCC.·-preserving F-CCC.[]-preserving (F.₁ (! ∷ 𝓏))) CC.𝓏 (flip-transport′ (F.₁ (! ∷ 𝓏)) CC.𝓏 F-CCC.𝓏-preserving))) ⟩
                  transport (PE.cong (CC._· A) (I {Γ})) PE.refl (transport F-CCC.·-preserving F-CCC.[]-preserving (F.₁ (! ∷ 𝓏))) 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (reflexive (transport-trans {p₁ = F-CCC.·-preserving} {PE.cong (CC._· A) I} {F-CCC.[]-preserving} {PE.refl} (F.₁ (! ∷ 𝓏)))) ⟩
                  transport I (PE.trans F-CCC.[]-preserving PE.refl) (F.₁ (! ∷ 𝓏)) 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≈⟨ 𝒞.∘-resp-≈ˡ (reflexive (transport-≡₂ (F.₁ (! ∷ 𝓏)) PE.refl (trans-refl F-CCC.[]-preserving))) ⟩
                  transport I I (F.₁ (! ∷ 𝓏)) 𝒞.∘ transport I I (F.₁ (γ ∷ a))
                ≡⟨ transport-∘ (F.₁ (! ∷ 𝓏)) (F.₁ (γ ∷ a)) ⟩
                  transport I I (F.₁ (! ∷ 𝓏) 𝒞.∘ F.₁ (γ ∷ a))
                ≈⟨ transport-≈ (F.₁ (! ∷ 𝓏) 𝒞.∘ F.₁ (γ ∷ a)) (F.₁ ((! ∷ 𝓏) ∘ (γ ∷ a))) (sym F.homomorphism) ⟩
                  transport I I (F.₁ ((! ∷ 𝓏) ∘ (γ ∷ a)))
                ≈⟨ transport-≈ (F.₁ (! ∷ (𝓏 [ γ ∷ a ]))) (F.₁ (! ∷ a)) (F.F-resp-≈ (∷-congᵣ v𝓏)) ⟩
                  transport I I (F.₁ (! ∷ a))
                ≈⟨ flip-transport′ {p = I} {I} (F.₁ (! ∷ a)) ⟦ a ⟧C (⟦ a ⟧C-universal) ⟩
                  ⟦ a ⟧C
                ∎

    ⟦_⟧-univeral = ⟦_⟧S-universal

{-
    ⟦ 𝓏       ⟧C-universal₁ = begin
        F.₁ (! ∷ 𝓏)
      ≈⟨ F-CCC.𝓏-preserving ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym F-CCC.·-preserving) (PE.sym F-CCC.[]-preserving) CC.𝓏
      ≡⟨ {!!} ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) ⟦ 𝓏 ⟧C
      ∎
    ⟦ p γ     ⟧C-universal₁ = begin
        F.₁ (! ∷ p γ)
      ≈⟨ F.F-resp-≈ (S.trans (∷-congᵣ (p-cong (C.sym sb-id))) (S.sym π-lemma)) ⟩
        F.₁ ((! ∷ γ) Syntax.∘ Syntax.π Syntax.id)
      ≈⟨ F.homomorphism ⟩
        F.₁ (! ∷ γ) 𝒞.∘ F.₁ (Syntax.π Syntax.id)
      ≈⟨ 𝒞.∘-resp-≈ ⟦ γ ⟧C-universal₁ F-CCC.π-preserving ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) ⟦ γ ⟧C 𝒞.∘ PE.subst₂ 𝒞._⇒_ (PE.sym F-CCC.·-preserving) PE.refl CC.π
      ≡⟨ {!!} ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) (⟦ γ ⟧C 𝒞.∘ CC.π)
      ≡⟨⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) ⟦ p γ ⟧C
      ∎
    ⟦ Λ f     ⟧C-universal₁ = begin
        F.₁ (! ∷ Λ f)
      ≈⟨ F-CCC.Λ-preserving (! ∷ f) ⟩
        PE.subst₂ 𝒞._⇒_ PE.refl (PE.sym F-CCC.[]-preserving) (CCC.Λ (PE.subst₂ 𝒞._⇒_ F-CCC.·-preserving F-CCC.[]-preserving (F.₁ (! ∷ f))))
      ≈⟨ {!!} ⟩
        PE.subst₂ 𝒞._⇒_ PE.refl (PE.sym F-CCC.[]-preserving) (CCC.Λ (PE.subst₂ 𝒞._⇒_ (PE.cong (CC._· _) (PE.sym ⟦_⟧-universal₀)) PE.refl ⟦ f ⟧C))
      ≈⟨ {!!} ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) (CCC.Λ ⟦ f ⟧C)
      ≡⟨⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) ⟦ Λ f ⟧C
      ∎
    ⟦ f ⦅ x ⦆ ⟧C-universal₁ = begin
        F.₁ (! ∷ f ⦅ x ⦆)
      ≈⟨ F.F-resp-≈ (S.sym {!!}) ⟩
        F.₁ ((! ∷ p 𝓏 ⦅ 𝓏 ⦆) ∘ (! ∷ f ∷ x))
      ≈⟨ F.homomorphism ⟩
        F.₁ (! ∷ p 𝓏 ⦅ 𝓏 ⦆) 𝒞.∘ F.₁ (! ∷ f ∷ x)
      ≈⟨ 𝒞.∘-resp-≈ F-CCC.eval-preserving ⟦ ! ∷ f ∷ x ⟧-universal₁ ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) CCC.eval
          𝒞.∘ PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) CC.⟨ CC.⟨ CC.! , ⟦ f ⟧C ⟩ , ⟦ x ⟧C ⟩
      ≈⟨ {!!} ⟩
        PE.subst₂ 𝒞._⇒_ (PE.sym ⟦_⟧-universal₀) (PE.sym ⟦_⟧-universal₀) (CCC.eval 𝒞.∘ CC.⟨ ⟦ f ⟧C , ⟦ x ⟧C ⟩)
      ∎
    ⟦ a [ γ ] ⟧C-universal₁ = {!!}

    ⟦ !     ⟧-universal₁ = {!!}
    ⟦ γ ∷ a ⟧-universal₁ = {! CC.Ext.unique {!!} {!!} !}
-}
