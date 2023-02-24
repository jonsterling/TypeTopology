

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module DomainTheory.Presentation.C-Ideal
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        {𝓤 𝓥 𝓦 : Universe}
       where

open import UF.Powerset
open import UF.ImageAndSurjection pt
open import Posets.Poset fe
open PosetAxioms

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Presentation.Presentation pt fe {𝓤} {𝓥} {𝓦}


-- TODO put this at the right place
Conjunction : (I : 𝓣' ̇) → (I → Ω 𝓣) → Ω (𝓣 ⊔ 𝓣')
Conjunction I ps = (∀ i → ps i holds) , Π-is-prop fe λ _ → holds-is-prop (ps _)

syntax Conjunction I (λ i → p) = ⋀ i ꞉ I , p

module C-Ideal
  (G : 𝓤 ̇)
  (_≲_ : G → G → 𝓣 ̇)
  (_◃_ : Cover-set G _≲_)
 where

  is-C-ideal : (G → Ω 𝓣') → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ̇
  is-C-ideal ℑ = downward-closed × cover-closed
   where
    downward-closed = ∀ x y → x ≲ y
      → x ∈ ℑ → y ∈ ℑ
    cover-closed = ∀ I x (U : I → G) → (x ◃ U) holds
      → (∀ y → y ∈image U → y ∈ ℑ)
      → x ∈ ℑ

  being-C-ideal-is-prop : (ℑ : G → Ω 𝓣') → is-prop (is-C-ideal ℑ)
  being-C-ideal-is-prop ℑ = ×-is-prop
    (Π₄-is-prop fe λ _ _ _ _ → ∈-is-prop ℑ _)
    (Π₅-is-prop fe λ _ _ _ _ _ → ∈-is-prop ℑ _)

  intersection-is-C-ideal : {I : 𝓥' ̇} (ℑs : I → G → Ω 𝓣')
    → (∀ i → is-C-ideal (ℑs i))
    → is-C-ideal λ g → ⋀ i ꞉ _ , ℑs i g
  intersection-is-C-ideal ℑs ιs = dc , cc
   where
    dc = λ x y x≲y x∈ℑs i → pr₁ (ιs i) x y x≲y (x∈ℑs i)
    cc = λ J g U g◃U c i → pr₂ (ιs i) J g U g◃U λ g' g'∈U → c g' g'∈U i

  C-Idl : ∀ 𝓣' → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ⁺ ̇
  C-Idl 𝓣' = Σ (is-C-ideal {𝓣' = 𝓣'})

  module _ {𝓣' : Universe} where
    carrier : C-Idl 𝓣' → G → Ω 𝓣'
    carrier (ℑ , _) = ℑ

    C-ideality : (𝓘 : C-Idl 𝓣') → is-C-ideal (carrier 𝓘)
    C-ideality (_ , ι) = ι

    _⊑_ : C-Idl 𝓣' → C-Idl 𝓣' → 𝓤 ⊔ 𝓣' ̇
    (ℑ , ℑ-is-ideal) ⊑ (𝔍 , 𝔍-is-ideal) = ℑ ⊆ 𝔍

  -- The impredicatively generated C-ideal from a set
  Generated : (𝓣' : Universe) → (G → Ω 𝓥') → C-Idl (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓥' ⊔ (𝓣' ⁺))
  Generated 𝓣' S = (λ g → ⋀ ((ℑ , _) , _) ꞉  -- Too messy
    (Σ (ℑ , _) ꞉ C-Idl 𝓣' , S ⊆ ℑ), ℑ g) ,
    intersection-is-C-ideal (pr₁ ∘ pr₁) (pr₂ ∘ pr₁)

  Generated-contains : (S : G → Ω 𝓥') → S ⊆ carrier (Generated 𝓣' S)
  Generated-contains S g g∈S ((ℑ , ι), S⊆ℑ) = S⊆ℑ g g∈S

  -- Universal property

\end{code}
