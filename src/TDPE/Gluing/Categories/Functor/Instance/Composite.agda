{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor

module TDPE.Gluing.Categories.Functor.Instance.Composite
  {o₁ o₂ o₃ ℓ₁ ℓ₂ ℓ₃ e₁ e₂ e₃}
  {𝒞 : Category o₁ ℓ₁ e₁}
  {𝒟 : Category o₂ ℓ₂ e₂}
  {ℰ : Category o₃ ℓ₃ e₃}
  {F : Functor 𝒞 𝒟}
  {G : Functor 𝒟 ℰ}
  where

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import TDPE.Gluing.Categories.Category.ContextualCartesian
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed
open import TDPE.Gluing.Categories.Functor.ContextualCartesian
open import TDPE.Gluing.Categories.Functor.ContextualCartesianClosed

open import TDPE.Gluing.Transport
open import TDPE.Gluing.Transport.Functor

private
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module ℰ = Category ℰ

  module F = Functor F
  module G = Functor G

∘-CC : ∀ {a} (𝒰 : Set a) {𝒞-CC : ContextualCartesian 𝒞 𝒰} {𝒟-CC : ContextualCartesian 𝒟 𝒰} {ℰ-CC : ContextualCartesian ℰ 𝒰}
       → CCFunctor 𝒰 𝒟-CC ℰ-CC G
       → CCFunctor 𝒰 𝒞-CC 𝒟-CC F
       → CCFunctor 𝒰 𝒞-CC ℰ-CC (G ∘F F)
∘-CC 𝒰 {𝒞-CC} {𝒟-CC} {ℰ-CC} G-CC F-CC = record
  { terminal-preserving = PE.trans (PE.cong G.₀ F-CC.terminal-preserving) G-CC.terminal-preserving
  ; ·-preserving = ·-preserving
  ; π-preserving = begin
      G.₁ (F.₁ (𝒞-CC.π))
    ≈⟨ G.F-resp-≈ F-CC.π-preserving ⟩
      G.₁ (transport′ 𝒟 F-CC.·-preserving PE.refl 𝒟-CC.π)
    ≡⟨ transport′-F G 𝒟-CC.π F-CC.·-preserving PE.refl ⟩
      transport′ ℰ (PE.cong G.₀ F-CC.·-preserving) PE.refl (G.₁ 𝒟-CC.π)
    ≈⟨ transport-≈ ℰ (G.₁ 𝒟-CC.π) (transport′ ℰ _ PE.refl ℰ-CC.π) G-CC.π-preserving ⟩
      transport′ ℰ (PE.cong G.₀ F-CC.·-preserving) PE.refl (transport′ ℰ _ PE.refl ℰ-CC.π)
    ≡⟨ transport′-trans ℰ {p₁ = PE.cong G.₀ F-CC.·-preserving} {G-CC.·-preserving} {PE.refl} {PE.refl} ℰ-CC.π ⟩
      transport′ ℰ ·-preserving PE.refl ℰ-CC.π
    ∎
  ; 𝓏-preserving = begin
      G.₁ (F.₁ (𝒞-CC.𝓏))
    ≈⟨ G.F-resp-≈ F-CC.𝓏-preserving ⟩
      G.₁ (transport′ 𝒟 F-CC.·-preserving F-CC.[]-preserving 𝒟-CC.𝓏)
    ≡⟨ transport′-F G 𝒟-CC.𝓏 F-CC.·-preserving F-CC.[]-preserving ⟩
      transport′ ℰ (PE.cong G.₀ F-CC.·-preserving) (PE.cong G.₀ F-CC.[]-preserving) (G.₁ 𝒟-CC.𝓏)
    ≈⟨ transport-≈ ℰ (G.₁ 𝒟-CC.𝓏) (transport′ ℰ G-CC.·-preserving G-CC.[]-preserving ℰ-CC.𝓏) G-CC.𝓏-preserving ⟩
      transport′ ℰ (PE.cong G.₀ F-CC.·-preserving) (PE.cong G.₀ F-CC.[]-preserving) (transport′ ℰ G-CC.·-preserving G-CC.[]-preserving ℰ-CC.𝓏)
    ≡⟨ transport′-trans ℰ {p₁ = PE.cong G.₀ F-CC.·-preserving} {G-CC.·-preserving} {PE.cong G.₀ F-CC.[]-preserving} {G-CC.[]-preserving} ℰ-CC.𝓏 ⟩
      transport′ ℰ ·-preserving (PE.trans (PE.cong G.₀ F-CC.[]-preserving) G-CC.[]-preserving) ℰ-CC.𝓏
    ≡⟨ transport-≡₂ ℰ ℰ-CC.𝓏 PE.refl (PE.cong PE.sym []-lemma) ⟩
      transport′ ℰ ·-preserving _ ℰ-CC.𝓏
    ∎
  }
  where module F-CC = CCFunctor F-CC
        module G-CC = CCFunctor G-CC

        module 𝒞-CC = ContextualCartesian 𝒞-CC
        module 𝒟-CC = ContextualCartesian 𝒟-CC
        module ℰ-CC = ContextualCartesian ℰ-CC

        ·-preserving : ∀ {Γ A} → G.₀ (F.₀ (Γ 𝒞-CC.· A)) ≡ G.₀ (F.₀ Γ) ℰ-CC.· A
        ·-preserving = PE.trans (PE.cong G.₀ F-CC.·-preserving) G-CC.·-preserving

        {- FIXME(@doctorn) this is duplicated below -}
        []-lemma : ∀ {A} → PE.trans (PE.cong G.₀ F-CC.[]-preserving) G-CC.[]-preserving
                      ≡ PE.trans (PE.trans (PE.cong G.₀ F-CC.·-preserving) G-CC.·-preserving)
                                 (PE.cong (ℰ-CC._· A) (PE.trans (PE.cong G.₀ F-CC.terminal-preserving) G-CC.terminal-preserving))
        []-lemma with F-CC.terminal-preserving | G-CC.terminal-preserving
        ... | PE.refl | PE.refl = begin
            PE.trans (PE.cong G.₀ (PE.trans F-CC.·-preserving PE.refl)) (PE.trans (G-CC.·-preserving) PE.refl)
          ≡⟨ PE.cong₂ PE.trans (PE.cong (PE.cong G.₀) (trans-refl 𝒟 F-CC.·-preserving)) (trans-refl ℰ _) ⟩
            PE.trans (PE.cong G.₀ F-CC.·-preserving) G-CC.·-preserving
          ≡⟨ PE.sym (trans-refl ℰ (PE.trans (PE.cong G.₀ F-CC.·-preserving) (G-CC.·-preserving))) ⟩
            PE.trans (PE.trans (PE.cong G.₀ F-CC.·-preserving) G-CC.·-preserving) PE.refl
          ∎
          where open PE.≡-Reasoning


        open ℰ.HomReasoning

∘-CCC : ∀ {a} (𝒰 : Set a) {𝒞-CCC : ContextualCartesianClosed 𝒞 𝒰} {𝒟-CCC : ContextualCartesianClosed 𝒟 𝒰} {ℰ-CCC : ContextualCartesianClosed ℰ 𝒰}
       → CCCFunctor 𝒰 𝒟-CCC ℰ-CCC G
       → CCCFunctor 𝒰 𝒞-CCC 𝒟-CCC F
       → CCCFunctor 𝒰 𝒞-CCC ℰ-CCC (G ∘F F)
∘-CCC 𝒰 {𝒞-CCC} {𝒟-CCC} {ℰ-CCC} G-CCC F-CCC = record
  { cartesian = ∘-CC _ G-CCC.cartesian F-CCC.cartesian
  ; Λ-preserving = λ h → begin
      G.₁ (F.₁ (𝒞-CCC.Λ h))
    ≈⟨ G.F-resp-≈ (F-CCC.Λ-preserving h) ⟩
      G.₁ (transport′ 𝒟 PE.refl F-CCC.[]-preserving (𝒟-CCC.Λ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h))))
    ≡⟨ transport′-F G (𝒟-CCC.Λ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h))) PE.refl _ ⟩
      transport′ ℰ PE.refl (PE.cong G.₀ F-CCC.[]-preserving) (G.₁ (𝒟-CCC.Λ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h))))
    ≈⟨
      transport-≈ ℰ
        {p = PE.refl}
        (G.₁ (𝒟-CCC.Λ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h))))
        (transport′ ℰ PE.refl G-CCC.[]-preserving (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (G.₁ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h))))))
        (G-CCC.Λ-preserving (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h)))
    ⟩
      transport′ ℰ PE.refl (PE.cong G.₀ F-CCC.[]-preserving)
        (transport′ ℰ PE.refl G-CCC.[]-preserving
          (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (G.₁ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h))))))
    ≡⟨
      transport′-trans ℰ {p₁ = PE.refl} {PE.refl} {PE.cong G.₀ F-CCC.[]-preserving} {G-CCC.[]-preserving}
        (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (G.₁ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h)))))
    ⟩
      transport′ ℰ PE.refl (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving)
        (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (G.₁ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h)))))
    ≈⟨
      transport-≈ ℰ
        (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (G.₁ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h)))))
        (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (transport ℰ (PE.cong G.₀ F-CCC.·-preserving) (PE.cong G.₀ F-CCC.[]-preserving) (G.₁ (F.₁ h)))))
        (ℰ-CCC.Λ-cong (transport-≈ ℰ (G.₁ (transport 𝒟 F-CCC.·-preserving F-CCC.[]-preserving (F.₁ h)))
          (transport ℰ (PE.cong G.₀ F-CCC.·-preserving)
          (PE.cong G.₀ F-CCC.[]-preserving) (G.₁ (F.₁ h)))
          (Category.Equiv.reflexive ℰ (transport-F G (F.₁ h) F-CCC.·-preserving F-CCC.[]-preserving))))
    ⟩
      transport′ ℰ PE.refl (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving)
        (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (transport ℰ (PE.cong G.₀ F-CCC.·-preserving) (PE.cong G.₀ F-CCC.[]-preserving) (G.₁ (F.₁ h)))))
    ≈⟨
      transport-≈ ℰ
        (ℰ-CCC.Λ (transport ℰ G-CCC.·-preserving G-CCC.[]-preserving (transport ℰ (PE.cong G.₀ F-CCC.·-preserving) (PE.cong G.₀ F-CCC.[]-preserving) (G.₁ (F.₁ h)))))
        (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving) (G.₁ (F.₁ h))))
        (ℰ-CCC.Λ-cong (Category.Equiv.reflexive ℰ (transport-trans ℰ {p₁ = PE.cong G.₀ F-CCC.·-preserving} {G-CCC.·-preserving} {PE.cong G.₀ F-CCC.[]-preserving} {G-CCC.[]-preserving} (G.₁ (F.₁ h)))))
    ⟩
      transport′ ℰ PE.refl (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving)
        (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving) (G.₁ (F.₁ h))))
    ≈⟨
      transport-≈ ℰ
        (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving) (G.₁ (F.₁ h))))
        (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving GF-CC.[]-preserving (G.₁ (F.₁ h))))
        (ℰ-CCC.Λ-cong (Category.Equiv.reflexive ℰ (transport-≡₂ ℰ (G.₁ (F.₁ h)) PE.refl []-lemma)))
    ⟩
      transport′ ℰ PE.refl (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving) (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving GF-CC.[]-preserving (G.₁ (F.₁ h))))
    ≡⟨ transport-≡₂ ℰ (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving GF-CC.[]-preserving (G.₁ (F.₁ h)))) PE.refl (PE.cong PE.sym []-lemma) ⟩
      transport′ ℰ PE.refl GF-CC.[]-preserving (ℰ-CCC.Λ (transport ℰ GF-CC.·-preserving GF-CC.[]-preserving (G.₁ (F.₁ h))))
    ∎
  ; eval-preserving = begin
      G.₁ (F.₁ 𝒞-CCC.eval)
    ≈⟨ G.F-resp-≈ F-CCC.eval-preserving ⟩
      G.₁ (transport′ 𝒟 (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· _) F-CCC.[]-preserving)) F-CCC.[]-preserving 𝒟-CCC.eval)
    ≡⟨ transport′-F G 𝒟-CCC.eval (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· _) F-CCC.[]-preserving)) F-CCC.[]-preserving ⟩
      transport′ ℰ (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· _) F-CCC.[]-preserving))) (PE.cong G.₀ F-CCC.[]-preserving) (G.₁ 𝒟-CCC.eval)
    ≈⟨
      transport-≈ ℰ
        (G.₁ 𝒟-CCC.eval)
        (transport′ ℰ (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· _) G-CCC.[]-preserving)) G-CCC.[]-preserving ℰ-CCC.eval)
        G-CCC.eval-preserving
    ⟩
      transport′ ℰ (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· _) F-CCC.[]-preserving))) (PE.cong G.₀ F-CCC.[]-preserving)
        (transport′ ℰ (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· _) G-CCC.[]-preserving)) G-CCC.[]-preserving ℰ-CCC.eval)
    ≡⟨
      transport′-trans ℰ
        {p₁ = PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· _) F-CCC.[]-preserving))}
        {PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· _) G-CCC.[]-preserving)}
        {PE.cong G.₀ F-CCC.[]-preserving}
        {G-CCC.[]-preserving}
        ℰ-CCC.eval
    ⟩
      transport′ ℰ
        (PE.trans (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· _) F-CCC.[]-preserving))) (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· _) G-CCC.[]-preserving)))
        (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving)
        ℰ-CCC.eval
    ≡⟨ transport-≡₂ ℰ ℰ-CCC.eval (PE.cong PE.sym II) (PE.cong PE.sym []-lemma) ⟩
      transport′ ℰ (PE.trans GF-CC.·-preserving (PE.cong (ℰ-CCC._· _) GF-CC.[]-preserving)) GF-CC.[]-preserving ℰ-CCC.eval
    ∎
  }
  where module F-CCC = CCCFunctor F-CCC
        module G-CCC = CCCFunctor G-CCC
        module GF-CC = CCFunctor (∘-CC _ G-CCC.cartesian F-CCC.cartesian)

        module 𝒞-CCC = ContextualCartesianClosed 𝒞-CCC
        module 𝒟-CCC = ContextualCartesianClosed 𝒟-CCC
        module ℰ-CCC = ContextualCartesianClosed ℰ-CCC

        []-lemma : ∀ {A} → PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving ≡ GF-CC.[]-preserving {A}
        []-lemma with F-CCC.terminal-preserving | G-CCC.terminal-preserving
        ... | PE.refl | PE.refl = begin
            PE.trans (PE.cong G.₀ (PE.trans F-CCC.·-preserving PE.refl)) (PE.trans (G-CCC.·-preserving) PE.refl)
          ≡⟨ PE.cong₂ PE.trans (PE.cong (PE.cong G.₀) (trans-refl 𝒟 F-CCC.·-preserving)) (trans-refl ℰ _) ⟩
            PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving
          ≡⟨ PE.sym (trans-refl ℰ (PE.trans (PE.cong G.₀ F-CCC.·-preserving) (G-CCC.·-preserving))) ⟩
            PE.trans (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving) PE.refl
          ∎
          where open PE.≡-Reasoning

        O : ∀ {Γ Γ'} {A} (p : Γ ≡ Γ') →
            PE.trans (PE.cong G.₀ (PE.cong (𝒟-CCC._· A) p)) G-CCC.·-preserving
              ≡ PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) (PE.cong G.₀ p))
        O PE.refl = PE.sym (trans-refl ℰ _)

        I : ∀ {A B} →
            PE.trans
              (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· A) (F-CCC.[]-preserving {B}))))
              (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.[]-preserving))
            ≡
            PE.trans
              (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving)
              (PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving))
        I {A} {B} with F-CCC.terminal-preserving | G-CCC.terminal-preserving
        ... | PE.refl | PE.refl = begin
            PE.trans
              (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· A) (PE.trans F-CCC.·-preserving PE.refl))))
              (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) (PE.trans G-CCC.·-preserving PE.refl)))
          ≡⟨
            PE.cong₂ PE.trans
              (PE.cong (PE.cong G.₀) (PE.cong (PE.trans F-CCC.·-preserving) (PE.cong (PE.cong (𝒟-CCC._· A)) (trans-refl 𝒟 F-CCC.·-preserving))))
              (PE.cong (PE.trans G-CCC.·-preserving) (PE.cong (PE.cong (ℰ-CCC._· A)) (trans-refl ℰ G-CCC.·-preserving)))
          ⟩
            PE.trans
              (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· A) F-CCC.·-preserving)))
              (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving))
          ≡⟨
            PE.cong (λ x → PE.trans x (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving)))
              (trans-cong 𝒟 {p = F-CCC.·-preserving} {PE.cong (𝒟-CCC._· A) F-CCC.·-preserving} G.₀)
          ⟩
            PE.trans
              (PE.trans (PE.cong G.₀ F-CCC.·-preserving) (PE.cong G.₀ (PE.cong (𝒟-CCC._· A) F-CCC.·-preserving)))
              (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving))
          ≡⟨
            PE.sym (trans-assoc ℰ
              {p = PE.cong G.₀ F-CCC.·-preserving}
              {PE.cong G.₀ (PE.cong (𝒟-CCC._· A) F-CCC.·-preserving)}
              {PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving)})
          ⟩
            PE.trans
              (PE.cong G.₀ F-CCC.·-preserving)
              (PE.trans (PE.cong G.₀ (PE.cong (𝒟-CCC._· A) F-CCC.·-preserving)) (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving)))
          ≡⟨
            PE.cong (PE.trans (PE.cong G.₀ F-CCC.·-preserving)) (trans-assoc ℰ
              {p = PE.cong G.₀ (PE.cong (𝒟-CCC._· A) F-CCC.·-preserving)}
              {G-CCC.·-preserving}
              {PE.cong (ℰ-CCC._· A) G-CCC.·-preserving})
          ⟩
            PE.trans
              (PE.cong G.₀ F-CCC.·-preserving)
              (PE.trans (PE.trans (PE.cong G.₀ (PE.cong (𝒟-CCC._· A) F-CCC.·-preserving)) G-CCC.·-preserving) (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving))
          ≡⟨ PE.cong (PE.trans (PE.cong G.₀ F-CCC.·-preserving)) (PE.cong (λ x → PE.trans x (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving)) (O F-CCC.·-preserving)) ⟩
            PE.trans
              (PE.cong G.₀ F-CCC.·-preserving)
              (PE.trans (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) (PE.cong G.₀ F-CCC.·-preserving))) (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving))
          ≡⟨
            PE.cong (PE.trans (PE.cong G.₀ F-CCC.·-preserving))
              (PE.sym (trans-assoc ℰ
                {p = G-CCC.·-preserving}
                {PE.cong (ℰ-CCC._· A) (PE.cong G.₀ F-CCC.·-preserving)}
                {PE.cong (ℰ-CCC._· A) G-CCC.·-preserving}))
          ⟩
            PE.trans
              (PE.cong G.₀ F-CCC.·-preserving)
              (PE.trans G-CCC.·-preserving (PE.trans (PE.cong (ℰ-CCC._· A) (PE.cong G.₀ F-CCC.·-preserving)) (PE.cong (ℰ-CCC._· A) G-CCC.·-preserving)))
          ≡⟨
            PE.cong (PE.trans (PE.cong G.₀ F-CCC.·-preserving)) (PE.cong (PE.trans G-CCC.·-preserving)
              (PE.sym (trans-cong ℰ {p = PE.cong G.₀ F-CCC.·-preserving} {G-CCC.·-preserving} (ℰ-CCC._· A))))
          ⟩
            PE.trans
              (PE.cong G.₀ F-CCC.·-preserving)
              (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving)))
          ≡⟨
            trans-assoc ℰ
              {p = PE.cong G.₀ F-CCC.·-preserving}
              {G-CCC.·-preserving}
              {PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving)}
          ⟩
            PE.trans
              (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving)
              (PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving))
          ≡⟨
            PE.cong (PE.trans GF-CC.·-preserving)
              (PE.cong (PE.cong (ℰ-CCC._· A))
                (PE.cong₂ PE.trans (PE.cong (PE.cong G.₀) (PE.sym (trans-refl 𝒟 F-CCC.·-preserving))) (PE.sym (trans-refl ℰ G-CCC.·-preserving))))
          ⟩
            PE.trans
              GF-CC.·-preserving
              (PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ (PE.trans F-CCC.·-preserving PE.refl))
                (PE.trans G-CCC.·-preserving PE.refl)))
          ∎
          where open PE.≡-Reasoning

        II : ∀ {A B} → PE.trans
                        (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· A) (F-CCC.[]-preserving {B}))))
                        (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.[]-preserving))
                      ≡ PE.trans GF-CC.·-preserving (PE.cong (ℰ-CCC._· A) GF-CC.[]-preserving)
        II {A} {B} = begin
            PE.trans
              (PE.cong G.₀ (PE.trans F-CCC.·-preserving (PE.cong (𝒟-CCC._· A) (F-CCC.[]-preserving {B}))))
              (PE.trans G-CCC.·-preserving (PE.cong (ℰ-CCC._· A) G-CCC.[]-preserving))
          ≡⟨ I ⟩
            PE.trans
              (PE.trans (PE.cong G.₀ F-CCC.·-preserving) G-CCC.·-preserving)
              (PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving))
          ≡⟨⟩
            PE.trans GF-CC.·-preserving (PE.cong (ℰ-CCC._· A) (PE.trans (PE.cong G.₀ F-CCC.[]-preserving) G-CCC.[]-preserving))
          ≡⟨ PE.cong (PE.trans GF-CC.·-preserving) (PE.cong (PE.cong (ℰ-CCC._· A)) []-lemma) ⟩
            PE.trans GF-CC.·-preserving (PE.cong (ℰ-CCC._· A) GF-CC.[]-preserving)
          ∎
          where open PE.≡-Reasoning

        open ℰ.HomReasoning
