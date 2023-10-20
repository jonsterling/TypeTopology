Jon Sterling and Mike Shulman, September 2023.

\begin{code}
{-# OPTIONS --safe --without-K --exact-split #-}

module WildCategories.Base where

open import MLTT.Spartan
open import UF.Subsingletons

record WildCategory 𝓤 𝓥 : (𝓤 ⊔ 𝓥)⁺ ̇ where
 field
  ob : 𝓤 ̇
  hom : ob → ob → 𝓥 ̇
  idn : (x : ob) → hom x x
  _<<_ : {x y z : ob} (g : hom y z) (f : hom x y) → hom x z
  assoc
   : {u v w x : ob} (f : hom u v) (g : hom v w) (h : hom w x)
   → h << (g << f) ＝ (h << g) << f
  runit
   : {x y : ob} (f : hom x y)
   → f << idn x ＝ f
  lunit
   : {x y : ob} (f : hom x y)
   → idn y << f ＝ f

module _ {𝓤 𝓥} (C : WildCategory 𝓤 𝓥) where
 open WildCategory C

 is-initial-object : ob → 𝓤 ⊔ 𝓥 ̇
 is-initial-object I = (x : ob) → is-singleton (hom I x)

 has-initial-object : 𝓤 ⊔ 𝓥 ̇
 has-initial-object = Σ is-initial-object

module _ {𝓤} where
 open WildCategory

 TYPE : WildCategory (𝓤 ⁺) 𝓤
 ob TYPE = 𝓤 ̇
 hom TYPE A B = A → B
 idn TYPE A x = x
 _<<_ TYPE g f x = g (f x)
 assoc TYPE _ _ _ = refl
 runit TYPE _ = refl
 lunit TYPE _ = refl

module _ {𝓤 𝓥 𝓦 𝓧} (C : WildCategory 𝓤 𝓥) (D : WildCategory 𝓦 𝓧) where

 module C = WildCategory C
 module D = WildCategory D

 record WildFunctor : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓧) ̇ where
  field
   ob : C.ob → D.ob
   hom : {x y : C.ob} (f : C.hom x y) → D.hom (ob x) (ob y)
   idn : (x : C.ob) → hom (C.idn x) ＝ D.idn (ob x)
   cmp
    : {x y z : C.ob} (g : C.hom y z) (f : C.hom x y)
    → hom (g C.<< f) ＝ hom g D.<< hom f

  field
   lunit
    : {x y : C.ob} (f : C.hom x y)
    → ap hom (C.lunit f)
    ＝ cmp (C.idn y) f ∙ ap (D._<< hom f) (idn y) ∙ D.lunit (hom f)

   runit
    : {x y : C.ob} (f : C.hom x y)
    → ap hom (C.runit f)
    ＝ cmp f (C.idn x) ∙ ap (hom f D.<<_) (idn x) ∙ D.runit (hom f)

   assoc
    : {u v w x : C.ob} (f : C.hom u v) (g : C.hom v w) (h : C.hom w x)
    → ap hom (C.assoc f g h) ∙ cmp (h C.<< g) f ∙ ap (D._<< hom f) (cmp h g)
    ＝ cmp h (g C.<< f)
       ∙ ap (hom h D.<<_) (cmp g f)
       ∙ D.assoc (hom f) (hom g) (hom h)


\end{code}
