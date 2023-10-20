Jon Sterling and Mike Shulman, September 2023.

\begin{code}
{-# OPTIONS --safe --without-K --exact-split #-}

module WildCategories.Base where

open import MLTT.Spartan renaming (_∙_ to _∙'_; ap to ap')
open import UF.Subsingletons

infixl 2 _∙_
opaque
 _∙_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
 p ∙ q = p ∙' q

 ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ＝ x' → f x ＝ f x'
 ap = ap'

 sym : {X : 𝓤 ̇ } → {x y : X} → x ＝ y → y ＝ x
 sym p = p ⁻¹

 refl-∙ : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y) → refl ∙ p ＝ p
 refl-∙ refl = refl

 ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {x : X} → ap f refl ＝ refl {_} {Y} {f x}
 ap-refl = refl


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
  triangle
   : {x y z : ob} (f : hom x y) (g : hom y z)
   → assoc f (idn y) g ∙ ap (_<< f) (runit g) ＝ ap (g <<_) (lunit f)

 triangle'
  : {x y z : ob} (f : hom x y) (g : hom y z)
  → sym (assoc f (idn y) g) ∙ ap (g <<_) (lunit f) ＝ ap (_<< f) (runit g)
 triangle' = {!!}

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
 triangle TYPE f g = refl-∙ _ ∙ ap-refl ∙ sym ap-refl

module _ {𝓤 𝓥 𝓦 𝓧} (C : WildCategory 𝓤 𝓥) (D : WildCategory 𝓦 𝓧) where
 private
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


  runit'
   : {x y : C.ob} (f : C.hom x y)
   → D.runit (hom f) ＝ sym (ap (hom f D.<<_) (idn x)) ∙ sym (cmp f (C.idn x)) ∙ ap hom (C.runit f)
  runit' =  {!!}


module _ {𝓤 𝓥} (C : WildCategory 𝓤 𝓥) (F : WildFunctor C C) where
 module C = WildCategory C

 private
  module F = WildFunctor F

 record WildAlgebra : 𝓤 ⊔ 𝓥 ̇ where
  field
   car : C.ob
   alg : C.hom (F.ob car) car

 module _ (X Y : WildAlgebra) where
  private
   module X = WildAlgebra X
   module Y = WildAlgebra Y

  record WildAlgebraHom : 𝓤 ⊔ 𝓥 ̇ where
   field
    car : C.hom X.car Y.car
    alg : car C.<< X.alg ＝ Y.alg C.<< F.hom car

 module _ {X Y : WildAlgebra} (f g : WildAlgebraHom X Y) where
  private
   module X = WildAlgebra X
   module Y = WildAlgebra Y
   module f = WildAlgebraHom f
   module g = WildAlgebraHom g

  record WildAlgebraHomEquiv : 𝓤 ⊔ 𝓥 ̇ where
   field
    car : f.car ＝ g.car
    alg : f.alg ∙ ap (Y.alg C.<<_ ∘ F.hom) car ＝ ap (C._<< X.alg) car ∙ g.alg


 module ALG where
  module _ (X : WildAlgebra) where
   private
    module X = WildAlgebra X

   open WildAlgebraHom

   idn : WildAlgebraHom X X
   car idn = C.idn X.car
   alg idn =
    C.lunit X.alg
    ∙ sym (C.runit X.alg)
    ∙ ap (X.alg C.<<_) (sym (F.idn X.car))

  module _ (X Y Z : WildAlgebra) (g : WildAlgebraHom Y Z) (f : WildAlgebraHom X Y) where
   private
    module X = WildAlgebra X
    module Y = WildAlgebra Y
    module Z = WildAlgebra Z
    module f = WildAlgebraHom f
    module g = WildAlgebraHom g

   open WildAlgebraHom

   cmp : WildAlgebraHom X Z
   car cmp = g.car C.<< f.car
   alg cmp =
    sym (C.assoc X.alg f.car g.car)
    ∙ ap (g.car C.<<_) f.alg
    ∙ C.assoc (F.hom f.car) Y.alg g.car
    ∙ ap (C._<< F.hom f.car) g.alg
    ∙ sym (C.assoc (F.hom f.car) (F.hom g.car) Z.alg)
    ∙ ap (Z.alg C.<<_) (sym (F.cmp g.car f.car))

  module _ (X Y : WildAlgebra) (f : WildAlgebraHom X Y) where
   private
    module X = WildAlgebra X
    module Y = WildAlgebra Y
    module f = WildAlgebraHom f

   open WildAlgebraHomEquiv

   runit~ : WildAlgebraHomEquiv (cmp X X Y f (idn X)) f
   car runit~ = C.runit f.car
   alg runit~ =
    sym (C.assoc X.alg (C.idn X.car) f.car) ∙
     ap (C._<<_ f.car)
     (C.lunit X.alg ∙ sym (C.runit X.alg) ∙
      ap (C._<<_ X.alg) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ sym (C.assoc (F.hom (C.idn X.car)) (F.hom f.car) Y.alg)
     ∙ ap (C._<<_ Y.alg) (sym (F.cmp f.car (C.idn X.car)))
     ∙ ap (λ x → Y.alg C.<< F.hom x) (C.runit f.car)

    ＝⟨ {!!} ⟩

    sym (C.assoc X.alg (C.idn X.car) f.car) ∙
     ap (C._<<_ f.car) (C.lunit X.alg)
     ∙ ap (f.car C.<<_) (sym (C.runit X.alg) ∙ ap (C._<<_ X.alg) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ sym (C.assoc (F.hom (C.idn X.car)) (F.hom f.car) Y.alg)
     ∙ ap (C._<<_ Y.alg) (sym (F.cmp f.car (C.idn X.car)))
     ∙ ap (λ x → Y.alg C.<< F.hom x) (C.runit f.car)

    ＝⟨ {!!} ⟩

    ap (C._<< X.alg) (C.runit f.car)
     ∙ ap (f.car C.<<_) (sym (C.runit X.alg) ∙ ap (C._<<_ X.alg) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ sym (C.assoc (F.hom (C.idn X.car)) (F.hom f.car) Y.alg)
     ∙ ap (C._<<_ Y.alg) (sym (F.cmp f.car (C.idn X.car)))
     ∙ ap (λ x → Y.alg C.<< F.hom x) (C.runit f.car)

    ＝⟨ {!!} ⟩

    ap (C._<< X.alg) (C.runit f.car)
     ∙ ap (f.car C.<<_) (sym (C.runit X.alg))
     ∙ ap (f.car C.<<_) (ap (X.alg C.<<_) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ sym (C.assoc (F.hom (C.idn X.car)) (F.hom f.car) Y.alg)
     ∙ ap (Y.alg C.<<_) (sym (F.cmp f.car (C.idn X.car)))
     ∙ ap (Y.alg C.<<_ ∘ F.hom) (C.runit f.car)

    ＝⟨ {!!} ⟩

    ap (C._<< X.alg) (C.runit f.car)
     ∙ ap (f.car C.<<_) (sym (C.runit X.alg))
     ∙ ap (f.car C.<<_) (ap (X.alg C.<<_) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ sym (C.assoc (F.hom (C.idn X.car)) (F.hom f.car) Y.alg)
     ∙ ap (Y.alg C.<<_) (sym (F.cmp f.car (C.idn X.car)) ∙ ap F.hom (C.runit f.car))

    ＝⟨ {!!} ⟩ -- by lem0

    ap (C._<< X.alg) (C.runit f.car)
     ∙ ap (f.car C.<<_) (sym (C.runit X.alg))
     ∙ ap (f.car C.<<_) (ap (X.alg C.<<_) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ sym (C.assoc (F.hom (C.idn X.car)) (F.hom f.car) Y.alg)
     ∙ ap (Y.alg C.<<_) (ap (F.hom f.car C.<<_) (F.idn X.car) ∙ C.runit (F.hom f.car))

    ＝⟨ {!!} ⟩

    ap (C._<< X.alg) (C.runit f.car)
     ∙ ap (f.car C.<<_) (sym (C.runit X.alg))
     ∙ ap (f.car C.<<_) (ap (X.alg C.<<_) (sym (F.idn X.car)))
     ∙ C.assoc (F.hom (C.idn X.car)) X.alg f.car
     ∙ ap (C._<< F.hom (C.idn X.car)) f.alg
     ∙ {!!}

    ＝⟨ {!!} ⟩


    ap (C._<< X.alg) (C.runit f.car) ∙ f.alg ∎

    where
     lem0 : sym (F.cmp f.car (C.idn X.car)) ∙ ap F.hom (C.runit f.car) ＝ ap (F.hom f.car C.<<_) (F.idn X.car) ∙ C.runit (F.hom f.car)
     lem0 =
      sym (F.cmp f.car (C.idn X.car)) ∙ ap F.hom (C.runit f.car)

      ＝⟨ {!!} ⟩

      sym (F.cmp f.car (C.idn X.car)) ∙ (F.cmp f.car (C.idn X.car) ∙ ap (F.hom f.car C.<<_) (F.idn X.car) ∙ C.runit (F.hom f.car))

      ＝⟨ {!!} ⟩

      ap (F.hom f.car C.<<_) (F.idn X.car) ∙ C.runit (F.hom f.car) ∎




  -- This will not have the triangle law!
  ALG : WildCategory (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
  WildCategory.ob ALG = WildAlgebra
  WildCategory.hom ALG = WildAlgebraHom
  WildCategory.idn ALG = idn
  WildCategory._<<_ ALG = cmp _ _ _
  WildCategory.assoc ALG = {!!}
  WildCategory.runit ALG = {!!}
  WildCategory.lunit ALG = {!!}
  WildCategory.triangle ALG = {!!}

\end{code}
