\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑) hiding (max)
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.FunExt
open import UF.Miscelanea
open import UF.Equiv

module TWA.Thesis.Chapter6.SequenceContinuity (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe

open import MLTT.Two-Properties

seq-f-ucontinuous¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y)) → 𝓤 ⊔ 𝓥 ̇
seq-f-ucontinuous¹ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ δ ꞉ ℕ , ((x₁ x₂ : (ℕ → X))
 → (x₁ ∼ⁿ x₂) δ → (f x₁ ∼ⁿ f x₂) ϵ)

seq-f-ucontinuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                   → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
seq-f-ucontinuous² {𝓤} {𝓥} {𝓦} {X} {Y} f
 = (ϵ : ℕ) → Σ (δˣ , δʸ) ꞉ ℕ × ℕ ,
   ((x₁ x₂ : (ℕ → X)) (y₁ y₂ : (ℕ → Y))
 → (x₁ ∼ⁿ x₂) δˣ → (y₁ ∼ⁿ y₂) δʸ → (f x₁ y₁ ∼ⁿ f x₂ y₂) ϵ)

seq-f-ucontinuous¹²-comp
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ }
 → (f : (ℕ → Z) → (ℕ → W))
 → (g : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous¹ f → seq-f-ucontinuous² g
 → seq-f-ucontinuous² λ x y → f (g x y)
seq-f-ucontinuous¹²-comp {_} {_} {_} {_} {X} {Y} {Z} {W}
 f g ϕᶠ ϕᵍ ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = pr₁ (ϕᵍ (pr₁ (ϕᶠ ϵ)))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ) → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f (g x₁ y₁) ∼ⁿ f (g x₂ y₂)) ϵ
  γ x₁ x₂ y₁ y₂ x∼ y∼
    = pr₂ (ϕᶠ ϵ) (g x₁ y₁) (g x₂ y₂)
        (pr₂ (ϕᵍ (pr₁ (ϕᶠ ϵ))) x₁ x₂ y₁ y₂ x∼ y∼)

seq-f-ucontinuousᴺ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
                   → 𝓤 ⊔ 𝓥  ̇
seq-f-ucontinuousᴺ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ (d , δ) ꞉ ℕ × ℕ ,
   ((x₁ x₂ : (ℕ → (ℕ → X)))
 → ((n : ℕ) → n < d → (x₁ n ∼ⁿ x₂ n) δ) → (f x₁ ∼ⁿ f x₂) ϵ)

∼ⁿ-to-C : {X : 𝓤 ̇ } → (d : is-discrete X)
        → (α β : (ℕ → X)) (n : ℕ)
        → (α ∼ⁿ β) n → C (ℕ→D-ClosenessSpace d) n α β
∼ⁿ-to-C d α β (succ n) α∼ⁿβ i i<n
 = is-decreasing' (discrete-seq-clofun d α β)
     n i (⊏-gives-< i (succ n) i<n)
     (decidable-𝟚₁ (discrete-decidable-seq d α β (succ n)) α∼ⁿβ)

C-to-∼ⁿ : {X : 𝓤 ̇ } → (d : is-discrete X)
        → (α β : (ℕ → X)) (n : ℕ)
        → C (ℕ→D-ClosenessSpace d) n α β → (α ∼ⁿ β) n
C-to-∼ⁿ d α β (succ n) Cαβ i i<n
 = 𝟚-decidable₁ (discrete-decidable-seq d α β (succ n))
     (Cαβ n (<-gives-⊏ n (succ n) (<-succ n))) i i<n

seq-f-ucontinuous¹-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → X) → (ℕ → Y))
 → seq-f-ucontinuous¹ f
 → f-ucontinuous (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ) f
seq-f-ucontinuous¹-to-closeness dˣ dʸ f ϕ ε
 = pr₁ (ϕ ε)
 , λ α β Cαβ → ∼ⁿ-to-C dʸ (f α) (f β) ε
                (pr₂ (ϕ ε) α β (C-to-∼ⁿ dˣ α β (pr₁ (ϕ ε)) Cαβ))

seq-f-ucontinuous²-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y) (dᶻ : is-discrete Z)
 → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous² f
 → f-ucontinuous (×-ClosenessSpace (ℕ→D-ClosenessSpace dˣ)
                                   (ℕ→D-ClosenessSpace dʸ))
                 (ℕ→D-ClosenessSpace dᶻ) (uncurry f)
seq-f-ucontinuous²-to-closeness dˣ dʸ dᶻ f ϕ ε
 = δ 
 , λ (α₁ , α₂) (β₁ , β₂) Cαβ
 → ∼ⁿ-to-C dᶻ (f α₁ α₂) (f β₁ β₂) ε
     (pr₂ (ϕ ε) α₁ β₁ α₂ β₂
       (λ i i<δα → C-to-∼ⁿ dˣ α₁ β₁ δ
         (×-C-left (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           α₁ β₁ α₂ β₂ δ Cαβ)
         i (<-≤-trans i δα δ i<δα
              (max-≤-upper-bound δα δβ)))
       (λ i i<δβ → C-to-∼ⁿ dʸ α₂ β₂ δ
         (×-C-right (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           α₁ β₁ α₂ β₂ δ Cαβ)
         i (<-≤-trans i δβ δ i<δβ
             (max-≤-upper-bound' δβ δα))))
 where
  δα δβ δ : ℕ
  δα = pr₁ (pr₁ (ϕ ε))
  δβ = pr₂ (pr₁ (ϕ ε))
  δ  = max δα δβ

\end{code}
