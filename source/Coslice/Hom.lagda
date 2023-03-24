Jonathan Sterling, 22nd March 2023.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Coslice.Hom where

open import MLTT.Spartan
open import UF.Base
open import UF.Retracts
open import UF.Equiv
open import UF.Embeddings
open import UF.FunExt
open import UF.IdentitySystems
open import UF.PairFun as PairFun
open import UF.Subsingletons
open import UF.EquivalenceExamples
open import Coslice.Type

module _ {A : 𝓤 ̇ } where
 Hom-Str-Type : Coslice A → Coslice A → 𝓤 ̇
 Hom-Str-Type X Y = target X → target Y

 Hom-Coh-Type : (X Y : Coslice A) → Hom-Str-Type X Y → 𝓤 ̇
 Hom-Coh-Type X Y f = alg Y ∼ f ∘ alg X

 Hom : Coslice A → Coslice A → 𝓤 ̇
 Hom X Y = Σ f ꞉ Hom-Str-Type X Y , Hom-Coh-Type X Y f

 hom-fun : {X Y : Coslice A} → Hom X Y → Hom-Str-Type X Y
 hom-fun (f , α[f]) = f

 hom-alg : {X Y : Coslice A} (f : Hom X Y) → Hom-Coh-Type X Y (hom-fun f)
 hom-alg (f , α[f]) = α[f]

 module _ {X Y : Coslice A} (f g : Hom X Y) where
  Homotopy-Str-Type : 𝓤 ̇
  Homotopy-Str-Type = hom-fun f ∼ hom-fun g

  Homotopy-Coh-Type : Homotopy-Str-Type → 𝓤 ̇
  Homotopy-Coh-Type ϕ = Π a ꞉ A , hom-alg g a ＝ hom-alg f a ∙ ϕ (alg X a)

  Hom-≈ : 𝓤 ̇
  Hom-≈ = Σ Homotopy-Coh-Type

 module _ (fe : FunExt) (X Y : Coslice A) (f : Hom X Y) where
  open Id-Sys
  open Has-Id-Sys
  open Dep-Id-Sys
  private [f] = homotopy-id-sys (fe 𝓤 𝓤) (hom-fun f)
  private module [f] = Id-Sys [f]

  private
   Aux =
    Σ ϕ ꞉ Hom-Coh-Type X Y (hom-fun f) ,
    Homotopy-Coh-Type f (hom-fun f , ϕ) (λ _ → refl)

   Aux-singleton-type : singleton-type' (dfunext (fe 𝓤 𝓤) (hom-alg f)) ≃ Aux
   Aux-singleton-type =
    pair-fun-equiv (happly , fe 𝓤 𝓤 _ _) λ h →
    (ap happly ,
     embedding-gives-embedding' _ (equivs-are-embeddings _ (fe 𝓤 𝓤 _ _)) _ _)
    ● (_∙ happly-funext (fe 𝓤 𝓤) _ _ (hom-alg f)) ,
        ∙-is-equiv-right (happly-funext (fe 𝓤 𝓤) _ _ (hom-alg f))
    ● happly-≃ (fe 𝓤 𝓤)

   abstract
    Aux-retract-singleton : Aux ◁ singleton-type' (dfunext (fe 𝓤 𝓤) (hom-alg f))
    Aux-retract-singleton = ≃-gives-◁ (≃-sym Aux-singleton-type)

    Aux-is-prop : is-prop Aux
    Aux-is-prop =
     retract-of-prop
      Aux-retract-singleton
      (singletons-are-props
       (singleton-types'-are-singletons _))

  hom-coh-id-sys : Dep-Id-Sys (Hom-Str-Type X Y) (Hom-Coh-Type X Y) [f] (hom-alg f)
  fam hom-coh-id-sys g ϕ α[g] = Homotopy-Coh-Type f (g , α[g]) ϕ
  ctr (sys hom-coh-id-sys) a = refl
  ind (sys hom-coh-id-sys) P p α[f] H =
   transport (uncurry P) (Aux-is-prop _ _) p
  ind-β (sys hom-coh-id-sys) P p =
   ap (λ - → transport (uncurry P) - p) lem
   where
    lem : Aux-is-prop (hom-alg f , λ _ → refl) (hom-alg f , λ _ → refl) ＝ refl
    lem = props-are-sets Aux-is-prop _ _

  hom-id-sys : Id-Sys (Hom X Y) f
  hom-id-sys = pair-id-sys [f] hom-coh-id-sys

 module _ (fe : FunExt) (X Y : Coslice A) (f g : Hom X Y) where
  private
   [f] = hom-id-sys fe X Y f
   module [f] = Id-Sys [f]

  from-hom-≈ : Hom-≈ f g → f ＝ g
  from-hom-≈ = [f].to-＝ g

  to-hom-≈-is-equiv : is-equiv from-hom-≈
  to-hom-≈-is-equiv = [f].to-＝-is-equiv g
\end{code}
