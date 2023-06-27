{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module TDPE.Gluing.Categories.Category.Instance.Presheaves
  {ℓ}
  (𝒞 : Category ℓ ℓ ℓ)
  where

open import Function.Equality using (_⟨$⟩_; cong)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Unit.Polymorphic as Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.Dependent
  using (_,_; proj₁; proj₂)

open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Yoneda
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Presheaves using (Presheaves)
open import Categories.Diagram.Pullback using (IsPullback; Pullback)

Psh = Presheaves {o′ = ℓ} {ℓ′ = ℓ} 𝒞

import TDPE.Gluing.Categories.Category.Instance.Setoids {ℓ} as S
open import TDPE.Gluing.Categories.Category.ContextualCartesian (Psh)
open import TDPE.Gluing.Categories.Category.ContextualCartesianClosed (Psh)

open Category Psh public
module 𝒞 = Category 𝒞

⊤ : Obj
⊤ = record
  { F₀ = λ _ → S.⊤
  ; F₁ = λ _ → Category.id (Setoids ℓ ℓ)
  ; identity = λ _ → tt
  ; homomorphism = λ _ → tt
  ; F-resp-≈ = λ _ _ → tt
  }

! : ∀ {P} → P ⇒ ⊤
! = record
  { η = λ _ → S.!
  ; commute = λ _ _ → tt
  ; sym-commute = λ _ _ → tt
  }

!-unique : ∀ {P} (h : P ⇒ ⊤) → h ≈ !
!-unique _ _ = tt

infixl 6 _×_

_×_ : Obj → Obj → Obj
Γ × A = record
 { F₀ = λ c → Γ.₀ c S.× A.₀ c
 ; F₁ = λ f → S.⟨ Γ.₁ f S.∘ S.π , A.₁ f S.∘ S.𝓏 ⟩
 ; identity = λ x → Γ.identity (proj₁ x) , A.identity (proj₂ x)
 ; homomorphism = λ x → (Γ.homomorphism (proj₁ x)) , (A.homomorphism (proj₂ x))
 ; F-resp-≈ = λ f≈g x → (Γ.F-resp-≈ f≈g (proj₁ x)) , (A.F-resp-≈ f≈g (proj₂ x))
 }
 where module Γ = Functor Γ
       module A = Functor A

_⊗_ : ∀ {P Q R} (α : P ⇒ R) (β : Q ⇒ R) → Pullback Psh α β
_⊗_ {P} {Q} {R} α β = record { isPullback = isPullback S._⊗_ }
  where module P = Functor P
        module Q = Functor Q
        module R = Functor R
        module α = NaturalTransformation α
        module β = NaturalTransformation β

        -- NOTE(@doctorn) don't use chosen pullbacks as Agda will try and compute too much
        module _ (_⊗₀_ : ∀ {A B C : S.Obj} (f : A S.⇒ C) (g : B S.⇒ C) → Pullback (Setoids ℓ ℓ) f g) where

          module _ c where
            module P⊗Q = Pullback (α.η c ⊗₀ β.η c)

          P⊗Q₀ : 𝒞.Obj → S.Obj
          P⊗Q₀ c = P⊗Q.P c

          commute : ∀ {d c} (f : c 𝒞.⇒ d)
                    → α.η c S.∘ P.₁ f S.∘ P⊗Q.p₁ d S.≈ β.η c S.∘ Q.₁ f S.∘ P⊗Q.p₂ d
          commute {d} {c} f = begin
              (α.η c S.∘ P.₁ f) S.∘ P⊗Q.p₁ d
            ≈⟨ S.∘-resp-≈ˡ {f = α.η c S.∘ P.₁ f} {h = R.₁ f S.∘ α.η d} {g = P⊗Q.p₁ d} (α.commute f) ⟩
              (R.₁ f S.∘ α.η d) S.∘ P⊗Q.p₁ d
            ≈⟨ S.sym-assoc {f = P⊗Q.p₁ d} {g = α.η d} {h = R.₁ f} ⟩
              R.₁ f S.∘ (α.η d S.∘ P⊗Q.p₁ d)
            ≈⟨ S.∘-resp-≈ʳ {f = α.η d S.∘ P⊗Q.p₁ d} {h = β.η d S.∘ P⊗Q.p₂ d} {g = R.₁ f} (P⊗Q.commute d) ⟩
              R.₁ f S.∘ (β.η d S.∘ P⊗Q.p₂ d)
            ≈⟨ S.assoc {f = P⊗Q.p₂ d} {g = β.η d} {h = R.₁ f} ⟩
              (R.₁ f S.∘ β.η d) S.∘ P⊗Q.p₂ d
            ≈⟨ S.∘-resp-≈ˡ {f = R.₁ f S.∘ β.η d} {h = β.η c S.∘ Q.₁ f} {g = P⊗Q.p₂ d} (β.sym-commute f) ⟩
              (β.η c S.∘ Q.₁ f) S.∘ P⊗Q.p₂ d
            ∎
            where open S.HomReasoning {P⊗Q.P d} {R.₀ c}

          P⊗Q₁ : ∀ {d c} (f : c 𝒞.⇒ d) → P⊗Q₀ d S.⇒ P⊗Q₀ c
          P⊗Q₁ {d} {c} f = P⊗Q.universal c {h₁ = P.₁ f S.∘ P⊗Q.p₁ d} {h₂ = Q.₁ f S.∘ P⊗Q.p₂ d} (commute f)

          identity : ∀ {c} → P⊗Q₁ (𝒞.id {c}) S.≈ S.id {P⊗Q₀ c}
          identity {c} {x} {y} p =
            P⊗Qc.sym (P⊗Q.unique c
              {i = S.id}
              (λ p → Pc.sym (Pc.trans (P.identity Pc.refl) (cong (P⊗Q.p₁ c) (P⊗Qc.sym p))))
              (λ p → Qc.sym (Qc.trans (Q.identity Qc.refl) (cong (P⊗Q.p₂ c) (P⊗Qc.sym p))))
              (P⊗Qc.sym p))
            where module P⊗Qc = Setoid (P⊗Q₀ c)
                  module Pc = Setoid (P.₀ c)
                  module Qc = Setoid (Q.₀ c)

          homomorphism : ∀ {c d e} {f : d 𝒞.⇒ c} {g : e 𝒞.⇒ d} → P⊗Q₁ (f 𝒞.∘ g) S.≈ P⊗Q₁ g S.∘ P⊗Q₁ f
          homomorphism {c} {d} {e} {f} {g} {x} {y} p =
            P⊗Qe.sym (P⊗Q.unique e
              {i = P⊗Q₁ g S.∘ P⊗Q₁ f}
              (λ p → Pe.sym (Pe.trans
                (P.homomorphism Pc.refl)
                (Pe.trans
                  (cong (P.₁ g) (Pd.sym (P⊗Q.p₁∘universal≈h₁ d p)))
                  (Pe.sym (P⊗Q.p₁∘universal≈h₁ e (cong (P⊗Q₁ f) P⊗Qc.refl))))))
              (λ p → Qe.sym (Qe.trans
                (Q.homomorphism Qc.refl)
                (Qe.trans (cong (Q.₁ g)
                  (Qd.sym (P⊗Q.p₂∘universal≈h₂ d p)))
                  (Qe.sym (P⊗Q.p₂∘universal≈h₂ e (cong (P⊗Q₁ f) P⊗Qc.refl))))))
              (P⊗Qc.sym p))
            where module P⊗Qc = Setoid (P⊗Q₀ c)
                  module P⊗Qe = Setoid (P⊗Q₀ e)
                  module Pc = Setoid (P.₀ c)
                  module Pd = Setoid (P.₀ d)
                  module Pe = Setoid (P.₀ e)
                  module Qc = Setoid (Q.₀ c)
                  module Qd = Setoid (Q.₀ d)
                  module Qe = Setoid (Q.₀ e)

          P⊗Q-resp-≈ : ∀ {c d} {f i : d 𝒞.⇒ c} → f 𝒞.≈ i → P⊗Q₁ f S.≈ P⊗Q₁ i
          P⊗Q-resp-≈ {c} {d} {f} {i} f≈i =
            P⊗Q.universal-resp-≈ d
              {h₁ = P.₁ f S.∘ P⊗Q.p₁ c} {h₂ = Q.₁ f S.∘ P⊗Q.p₂ c}
              {i₁ = P.₁ i S.∘ P⊗Q.p₁ c} {i₂ = Q.₁ i S.∘ P⊗Q.p₂ c}
              {eq = commute f} {eq′ = commute i}
              (S.∘-resp-≈ˡ {f = P.₁ f} {h = P.₁ i} {g = P⊗Q.p₁ c} (P.F-resp-≈ f≈i))
              (S.∘-resp-≈ˡ {f = Q.₁ f} {h = Q.₁ i} {g = P⊗Q.p₂ c} (Q.F-resp-≈ f≈i))

          α⊗β : Obj
          α⊗β = record
            { F₀ = P⊗Q₀
            ; F₁ = P⊗Q₁
            ; identity = identity
            ; homomorphism = homomorphism
            ; F-resp-≈ = P⊗Q-resp-≈
            }

          p₁ : α⊗β ⇒ P
          p₁ = ntHelper (record
            { η = λ c → P⊗Q.p₁ c
            ; commute = λ {_} {d} f p → P⊗Q.p₁∘universal≈h₁ d p
            })

          p₂ : α⊗β ⇒ Q
          p₂ = ntHelper (record
            { η = λ c → P⊗Q.p₂ c
            ; commute = λ {_} {d} f p → P⊗Q.p₂∘universal≈h₂ d p
            })

          module p₁ = NaturalTransformation p₁
          module p₂ = NaturalTransformation p₂

          universal-η : ∀ {A} {h₁ : A ⇒ P} {h₂ : A ⇒ Q} → α ∘ h₁ ≈ β ∘ h₂ → ∀ c → Functor.₀ A c S.⇒ P⊗Q₀ c
          universal-η {A} {h₁} {h₂} eq c =
            P⊗Q.universal c {h₁ = NaturalTransformation.η h₁ c} {h₂ = NaturalTransformation.η h₂ c} (eq {c})

          universal-commute : ∀ {A} {h₁ : A ⇒ P} {h₂ : A ⇒ Q} {eq : α ∘ h₁ ≈ β ∘ h₂}
                              → ∀ {c d} (f : c 𝒞.⇒ d)
                              → universal-η {A} {h₁} {h₂} eq c S.∘ Functor.₁ A f
                                  S.≈ P⊗Q₁ f S.∘ universal-η {A} {h₁} {h₂} eq d
          universal-commute {A} {h₁} {h₂} {eq} {c} {d} f {x} {y} p = begin
              universal-η {A} {h₁} {h₂} eq c ⟨$⟩ (A.₁ f ⟨$⟩ x)
            ≈⟨
              P⊗Q.unique c
                {i = universal-η {A} {h₁} {h₂} eq c S.∘ A.₁ f}
                (λ p → Pc.trans (P⊗Q.p₁∘universal≈h₁ c (Setoid.refl (A.₀ c))) (h₁.commute f p))
                (λ p → Qc.trans (P⊗Q.p₂∘universal≈h₂ c (Setoid.refl (A.₀ c))) (h₂.commute f p))
                p
            ⟩
              P⊗Q.universal c
                {h₁ = P.₁ f S.∘ h₁.η d}
                {h₂ = Q.₁ f S.∘ h₂.η d}
                (λ p → Rc.trans (α.commute f Pd.refl) (Rc.trans (cong (R.₁ f) (eq p)) (β.sym-commute f Qd.refl)))
              ⟨$⟩ y
            ≈⟨
              Setoid.sym (P⊗Q₀ c) (P⊗Q.unique c
                {i = P⊗Q₁ f S.∘ universal-η {A} {h₁} {h₂} eq d}
                (λ p → Pc.trans (p₁.commute f (Setoid.refl (P⊗Q₀ d))) (cong (P.₁ f) (P⊗Q.p₁∘universal≈h₁ d p)))
                (λ p → Qc.trans (p₂.commute f (Setoid.refl (P⊗Q₀ d))) (cong (Q.₁ f) (P⊗Q.p₂∘universal≈h₂ d p)))
                (Setoid.refl (A.₀ d)))
            ⟩
               P⊗Q₁ f ⟨$⟩ (universal-η {A} {h₁} {h₂} eq d ⟨$⟩ y)
            ∎
            where open Reasoning (P⊗Q₀ c)
                  module h₁ = NaturalTransformation h₁
                  module h₂ = NaturalTransformation h₂
                  module A = Functor A
                  module Pc = Setoid (P.₀ c)
                  module Pd = Setoid (P.₀ d)
                  module Qc = Setoid (Q.₀ c)
                  module Qd = Setoid (Q.₀ d)
                  module Rc = Setoid (R.₀ c)

          isPullback : IsPullback Psh p₁ p₂ α β
          isPullback = record
            { commute = λ {c} p → P⊗Q.commute c p
            ; universal = λ {A} {h₁} {h₂} eq → ntHelper (record
              { η = universal-η {A} {h₁} {h₂} eq
              ; commute = λ {c} {d} f p → universal-commute {A} {h₁} {h₂} {eq} f p
              })
            ; unique = λ {A} {h₁} {h₂} {i} {eq} p₁∘i≈h₁ p₂∘i≈h₂ {c} p →
               P⊗Q.unique c
                 {h₁ = NaturalTransformation.η h₁ c}
                 {h₂ = NaturalTransformation.η h₂ c}
                 {i = NaturalTransformation.η i c}
                 {eq {c}}
                 (p₁∘i≈h₁ {c})
                 (p₂∘i≈h₂ {c})
                 p
            ; p₁∘universal≈h₁ = λ {_} {_} {_} {_} {c} p → P⊗Q.p₁∘universal≈h₁ c p
            ; p₂∘universal≈h₂ = λ {_} {_} {_} {_} {c} p → P⊗Q.p₂∘universal≈h₂ c p
            }

unit : ∀ {A} → A ⇒ ⊤ × A
unit {A} = ntHelper (record
  { η = λ c → S.unit
  ; commute = λ f x → tt , cong (A.₁ f) x
  })
  where module A = Functor A

counit : ∀ {A} → ⊤ × A ⇒ A
counit {A} = ntHelper (record
  { η = λ c → S.counit
  ; commute = λ f x → cong (A.₁ f) (proj₂ x)
  })
  where module A = Functor A

fmap : ∀ {A B} → A ⇒ B → ⊤ × A ⇒ ⊤ × B
fmap f = unit ∘ f ∘ counit

⟨_,_⟩ : ∀ {Γ A} {Δ} → Δ ⇒ Γ → Δ ⇒ A → Δ ⇒ Γ × A
⟨ γ , a ⟩ = ntHelper (record
  { η = λ c → S.⟨ γ.η c , a.η c ⟩
  ; commute = λ f x → γ.commute f x , a.commute f x
  })
  where module γ = NaturalTransformation γ
        module a = NaturalTransformation a

π : ∀ {Γ A} → Γ × A ⇒ Γ
π {Γ} = record
  { η = λ c → S.π
  ; commute = λ f x → cong (Γ.₁ f) (proj₁ x)
  ; sym-commute = λ f x → cong (Γ.₁ f) (proj₁ x)
  }
  where module Γ = Functor Γ

𝓏 : ∀ {Γ A} → Γ × A ⇒ A
𝓏 {A = A} = record
  { η = λ c → S.𝓏
  ; commute = λ f x → cong (A.₁ f) (proj₂ x)
  ; sym-commute = λ f x → cong (A.₁ f) (proj₂ x)
  }
  where module A = Functor A

module 𝕪 = Functor (Yoneda.embed 𝒞)

Env : Obj → 𝒞.Obj → Obj
Env P c = P × 𝕪.₀ c

_^_ : Obj → Obj → Obj
P ^ Q = record
  { F₀ = λ c → hom-setoid {A = Env P c} {B = Q}
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ α → α ∘ ⟨ π , 𝕪.₁ f ∘ 𝓏 ⟩
    ; cong = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.∘-resp-≈ʳ (proj₂ x≈y))
    }
  ; identity = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.Equiv.trans 𝒞.identityˡ (proj₂ x≈y))
  ; homomorphism = λ α≈β x≈y → α≈β (proj₁ x≈y , 𝒞.Equiv.trans (𝒞.∘-resp-≈ʳ (proj₂ x≈y)) 𝒞.assoc)
  ; F-resp-≈ = λ f≈g α≈β x≈y → α≈β ((proj₁ x≈y) , (𝒞.∘-resp-≈ f≈g (proj₂ x≈y)))
  }

Λ : ∀ {Γ A B} → Γ × A ⇒ B → Γ ⇒ A ^ B
Λ {Γ} {A} {B} f = ntHelper (record
  { η = Λ-η
  ; commute = Λ-commute
  })
  where module Γ = Functor Γ
        module A = Functor A
        module B = Functor B
        module Γ×A = Functor (Γ × A)
        module A^B = Functor (A ^ B)
        module f = NaturalTransformation f

        α₀ : ∀ c → Setoid.Carrier (Γ.₀ c)
            → ∀ d → Setoid.Carrier (Functor.₀ (Env A c) d) → Setoid.Carrier (B.₀ d)
        α₀ c θ d (a , h) = f.η d ⟨$⟩ (Γ.₁ h ⟨$⟩ θ , a)

        α : ∀ c → Setoid.Carrier (Γ.₀ c)
            → ∀ d → (Functor.₀ (Env A c) d) S.⇒ B.₀ d
        α c θ d = record
          { _⟨$⟩_ = α₀ c θ d
          ; cong = λ x → cong (f.η d) (Γ.F-resp-≈ (proj₂ x) (Setoid.refl (Γ.₀ c)) , proj₁ x)
          }

        α-commute : ∀ c (θ : Setoid.Carrier (Γ.₀ c))
                    → ∀ {d e} (g : d 𝒞.⇒ e)
                    → α c θ d S.∘ Functor.₁ (Env A c) g S.≈ B.₁ g S.∘ α c θ e
        α-commute c θ {d} {e} g {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = begin
                  f.η d ⟨$⟩ (Γ.₁ (Functor.₁ (𝕪.₀ c) g ⟨$⟩ y₁) ⟨$⟩ θ , A.₁ g ⟨$⟩ x₁)
                ≈⟨ cong (f.η d) (Γ.F-resp-≈ 𝒞.identityˡ Γc.refl , Ad.refl) ⟩
                  f.η d ⟨$⟩ (Γ.₁ (y₁ 𝒞.∘ g) ⟨$⟩ θ , A.₁ g ⟨$⟩ x₁)
                ≈⟨ cong (f.η d) (Γ.homomorphism Γc.refl , Ad.refl) ⟩
                  f.η d ⟨$⟩ (Γ×A.₁ g ⟨$⟩ (Γ.₁ y₁ ⟨$⟩ θ , x₁))
                ≈⟨ f.commute g (Γ.F-resp-≈ y₁≈y₂ Γc.refl , x₁≈x₂) ⟩
                  B.₁ g ⟨$⟩ (f.η e ⟨$⟩ (Γ.₁ y₂ ⟨$⟩ θ , x₂))
                ∎
                where open Reasoning (B.₀ d)
                      module Γc = Setoid (Γ.₀ c)
                      module Ad = Setoid (A.₀ d)

        Λ-η₀ : ∀ c → Setoid.Carrier (Γ.₀ c) → Setoid.Carrier (A^B.₀ c)
        Λ-η₀ c θ = ntHelper (record
          { η = α c θ
          ; commute = α-commute c θ
          })

        Λ-η : ∀ c → Γ.₀ c S.⇒ A^B.₀ c
        Λ-η c = record
          { _⟨$⟩_ = Λ-η₀ c
          ; cong = λ θ≈θ′ x≈y → cong (f.η _) (Γ.F-resp-≈ (proj₂ x≈y) θ≈θ′ , proj₁ x≈y)
          }

        Λ-commute : ∀ {d e} (g : d 𝒞.⇒ e) → Λ-η d S.∘ Γ.₁ g S.≈ A^B.₁ g S.∘ Λ-η e
        Λ-commute {d} {e} g {θ} {θ′} θ≈θ′ {c} {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = begin
            f.η c ⟨$⟩ ((Γ.₁ y₁ ⟨$⟩ (Γ.₁ g ⟨$⟩ θ)) , x₁)
          ≈⟨ cong (f.η c) (Γ.F-resp-≈ y₁≈y₂ (Γ.F-resp-≈ 𝒞.Equiv.refl θ≈θ′) , Ac.refl) ⟩
            f.η c ⟨$⟩ ((Γ.₁ y₂ ⟨$⟩ (Γ.₁ g ⟨$⟩ θ′)) , x₁)
          ≈⟨ cong (f.η c) (Γc.sym (Γ.homomorphism Γe.refl) , x₁≈x₂) ⟩
            f.η c ⟨$⟩ (Γ.₁ (g 𝒞.∘ y₂) ⟨$⟩ θ′ , x₂)
          ∎
          where open Reasoning (B.₀ c)
                module Γc = Setoid (Γ.₀ c)
                module Γe = Setoid (Γ.₀ e)
                module Ac = Setoid (A.₀ c)

eval : ∀ {A B} → A ^ B × A ⇒ B
eval {A} {B} = ntHelper (record
  { η = eval-η
  ; commute = eval-commute
  })
  where module A^B×A = Functor (A ^ B × A)
        module A = Functor A
        module B = Functor B

        eval-η : ∀ c → A^B×A.₀ c S.⇒ B.₀ c
        eval-η c = record
          { _⟨$⟩_ = λ { (f , x) → NaturalTransformation.η f c ⟨$⟩ (x , 𝒞.id) }
          ; cong = λ { (f , x) → f (x , 𝒞.Equiv.refl) }
          }

        eval-commute : ∀ {c d} (g : c 𝒞.⇒ d) → eval-η c S.∘ A^B×A.₁ g S.≈ B.₁ g S.∘ eval-η d
        eval-commute {c} {d} g {f₁ , x₁} {f₂ , x₂} (f₁≈f₂ , x₁≈x₂) = begin
            f₁.η c ⟨$⟩ (A.₁ g ⟨$⟩ x₁ , g 𝒞.∘ 𝒞.id )
          ≈⟨
            cong (f₁.η c)
              ( Setoid.refl (A.₀ c)
              , 𝒞.Equiv.trans 𝒞.identityʳ (𝒞.Equiv.sym (𝒞.Equiv.trans 𝒞.identityˡ 𝒞.identityˡ))
              )
          ⟩
            f₁.η c ⟨$⟩ (Functor.₁ (Env A d) g ⟨$⟩ (x₁ , 𝒞.id))
          ≈⟨ f₁≈f₂ (A.F-resp-≈ 𝒞.Equiv.refl x₁≈x₂ , 𝒞.Equiv.refl) ⟩
            f₂.η c ⟨$⟩ (Functor.₁ (Env A d) g ⟨$⟩ (x₂ , 𝒞.id))
          ≈⟨ f₂.commute g (Setoid.refl (Functor.₀ (Env A d) d)) ⟩
            B.₁ g ⟨$⟩ (f₂.η d ⟨$⟩ (x₂ , 𝒞.id))
          ∎
          where open Reasoning (B.₀ c)

                module f₁ = NaturalTransformation f₁
                module f₂ = NaturalTransformation f₂

module _ {a} {𝒰 : Set a} where

  open import TDPE.Gluing.Contexts 𝒰 hiding (_⇒_)

  module _ (ι : 𝒰ᵀ → Obj) where

    CC : ContextualCartesian 𝒰ᵀ
    CC = record
      { terminal = record
        { ⊤ = ⊤
        ; ⊤-is-terminal = record { ! = ! ; !-unique = !-unique }
        }
      ; _·_ = λ Γ A → Γ × (ι A)
      ; π = λ {Γ} {A} → π {Γ} {ι A}
      ; 𝓏 = λ {Γ} {A} → unit ∘ 𝓏 {Γ} {ι A}
      ; extensions = record
        { ⟨_,_⟩ = λ {Δ} γ a → ⟨_,_⟩ {Δ = Δ} γ (counit ∘ a)
        ; project₁ = λ {Δ} {γ} {_} x → cong (NaturalTransformation.η γ _) x
        ; project₂ = λ {Δ} {_} {a} x → tt , proj₂ (cong (NaturalTransformation.η a _) x)
        ; unique = λ {Δ} {h} {γ} {a} x y z → unique {Δ = Δ} {h} {γ} {a} x y z
        }
      }
      where unique : ∀ {Γ A} {Δ} {h : Δ ⇒ Γ × A} {γ : Δ ⇒ Γ} {a : Δ ⇒ ⊤ × A}
                     → π ∘ h ≈ γ → unit ∘ 𝓏 ∘ h ≈ a → ⟨ γ , counit ∘ a ⟩ ≈ h
            unique {Γ} {A} {Δ} πh≈γ 𝓏h≈a {c} {x} {y} x≈y =
              Γc.sym (πh≈γ (Δc.sym x≈y)) , proj₂ (Ac.sym (𝓏h≈a (Δc.sym x≈y)))
              where module Γc = Setoid (Functor.₀ Γ c)
                    module Ac = Setoid (Functor.₀ (⊤ × A) c)
                    module Δc = Setoid (Functor.₀ Δ c)

  module _ (ι : 𝒰 → Obj) where

    private
      ⟦_⟧ : 𝒰ᵀ → Obj
      ⟦ A ⟧ = ⟦ A ⟧ᵀ ι _^_

    CCC : ContextualCartesianClosed 𝒰
    CCC = record
      { cartesian = CC ⟦_⟧
      ; Λ = λ {Γ} {A} {B} f → Λ′ {Γ} {⟦ A ⟧} {⟦ B ⟧} f
      ; eval = λ {A} {B} → eval′ {⟦ A ⟧} {⟦ B ⟧}
      ; β = λ {Γ} {A} {B} f → β {Γ} {⟦ A ⟧} {⟦ B ⟧} f
      ; unique = λ {Γ} {A} {B} {g} {h} → unique {Γ} {⟦ A ⟧} {⟦ B ⟧} {g} {h}
      }
      where Λ′ : ∀ {Γ A B} → Γ × A ⇒ ⊤ × B → Γ ⇒ ⊤ × A ^ B
            Λ′ f = unit ∘ Λ (counit ∘ f)

            eval′ : ∀ {A B} → ⊤ × (A ^ B) × A ⇒ ⊤ × B
            eval′ = unit ∘ eval ∘ ⟨ 𝓏 ∘ π , 𝓏 ⟩

            β : ∀ {Γ A B} (f : Γ × A ⇒ ⊤ × B) → eval′ ∘ ⟨ Λ′ f ∘ π , 𝓏 ⟩ ≈ f
            β {Γ} {A} {B} f x =
              cong (f.η _) (Setoid.trans (Γ×A.₀ _) (Γ.identity (Setoid.refl (Γ.₀ _)) , Setoid.refl (A.₀ _)) x)
              where module Γ = Functor Γ
                    module Γ×A = Functor (Γ × A)
                    module A = Functor A
                    module f = NaturalTransformation f

            unique : ∀ {Γ A B} {g : Γ × A ⇒ ⊤ × B} {h : Γ ⇒ ⊤ × A ^ B}
                     → eval′ ∘ ⟨ h ∘ π , 𝓏 ⟩ ≈ g
                     → h ≈ Λ′ g
            unique {Γ} {A} {B} {g} {h} ϵ⟨hπ,𝓏⟩≈g {c} {θ} {θ′} θ≈θ′ = tt , I
              where module A^B = Functor (A ^ B)
                    module h = NaturalTransformation h
                    module Λg = NaturalTransformation (Λ′ g)

                    I : Setoid._≈_ (A^B.₀ c) (proj₂ (h.η c ⟨$⟩ θ)) (proj₂ (Λg.η c ⟨$⟩ θ′))
                    I {d} {x₁ , y₁} {x₂ , y₂} (x₁≈x₂ , y₁≈y₂) = begin
                        πhcθ.η d ⟨$⟩ (x₁ , y₁)
                      ≈⟨ cong (πhcθ.η d) (Setoid.refl (A.₀ d) , 𝒞.Equiv.sym 𝒞.identityʳ) ⟩
                        πhcθ.η d ⟨$⟩ (x₁ , y₁ 𝒞.∘ 𝒞.id)
                      ≈⟨ proj₂ (h.sym-commute y₁ (Setoid.refl (Γ.₀ c))) (Setoid.refl (A.₀ d) , 𝒞.Equiv.refl) ⟩
                        πhdΓyθ.η d ⟨$⟩ (x₁ , 𝒞.id)
                      ≈⟨ proj₂ (ϵ⟨hπ,𝓏⟩≈g (Γ.F-resp-≈ y₁≈y₂ θ≈θ′ , x₁≈x₂)) ⟩
                        proj₂ (g.η d ⟨$⟩ (Γ.₁ y₂ ⟨$⟩ θ′ , x₂))
                      ∎
                      where module A = Functor A
                            module B = Functor B
                            module Γ = Functor Γ
                            module ⊤×A^B = Functor (⊤ × A ^ B)
                            module πhcθ = NaturalTransformation (proj₂ (h.η c ⟨$⟩ θ))
                            module πhdΓyθ = NaturalTransformation (proj₂ (h.η d ⟨$⟩ (Γ.₁ y₁ ⟨$⟩ θ)))
                            module g = NaturalTransformation g

                            open Reasoning (B.₀ d)
