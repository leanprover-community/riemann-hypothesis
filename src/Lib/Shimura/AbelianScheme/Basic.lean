module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
public import Lib.General.Geometry.LineBundles

/-!
# Abelian schemes: base change, finite kernels and constant functions

This file sets up abelian schemes over a base `S` in terms of `T`-points `T ⟶ A` in `Over S`,
written additively. It shows how points, sections and `O`-linear homomorphisms pass to a base
change. It proves that the kernel of a finite homomorphism into a separated commutative group scheme
over `Spec R` is `Spec S` for a finite `R`-algebra `S` (`New.Variety.exists_finite_kernel_ring`). It
also proves that global functions on the base change of an integral abelian scheme over a field to
an affine base are constant on the fibres (`New.Variety.hasConstFunctions_of_isPullback`).

## Main definitions and results

* `New.AddObj`, `New.ModuleObj O`: commutative group objects, and actions of a ring `O` on points.
* `New.IsGroupBaseChange`: base change, compatible with the group structure and the `O`-action;
  Mathlib's pullback carries both structures.
* `New.IsAbelianScheme`: smooth and proper, with surjective multiplication by every `m ≠ 0`.
  Divisibility is asked for where one usually asks for connected fibres.
* `New.Pic.atPoint`, `New.Pic.pairing`, `New.Pic.ParallelogramLaw`: for a class `c` in the Picard
  group `New.Pic` (written additively), its pull-back along a point, the pairing of two points, and
  the parallelogram law.

Notions from other files:
* `New.Pic.pull`: For p: Y → X, the homomorphism Pic X → Pic Y sending the class of a line bundle to
  the class of its pull-back.

## Relation to the literature

Known; see `Lib.Shimura.AbelianScheme.IsogenyFlatness` for sources.
-/

@[expose] public section

noncomputable section

/-! ## Abelian schemes, group base change and the Picard pairing -/

section AbelianScheme

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Adjunction
  CommRingCat Over Equiv Obj AddMonObj AddGrpObj Functor

namespace New

variable {S S' : Scheme.{0}} (b : S' ⟶ S) (O : outParam Type) [CommRing O] (A : Over S)

/-! ### Group objects, ring actions, base change, abelian schemes -/

/-- A commutative group object in schemes over `S`: an additive group object whose addition is
commutative. -/
class abbrev AddObj :=
  AddGrpObj A, IsCommAddMonObj A

attribute [instance] Hom.addCommGroup

export AddMonObj (comp_add add_comp comp_nsmul nsmul_comp comp_zero)

/-- An action of the commutative ring O on a commutative group object A: O-module structures on
all groups Hom(T, A), functorial in T. -/
class ModuleObj [AddObj A] where
  /-- For each `T` over `S`, the group of `T`-points of `A` is an `O`-module. -/
  [homModule (T : Over S) : Module O (T ⟶ A)]
  /-- The action is functorial in `T`: it commutes with pulling points back along `a : T' ⟶ T`. -/
  comp_smul {T' T : Over S} (a : T' ⟶ T) (c : O) (x : T ⟶ A) : a ≫ (c • x : T ⟶ A) = c • a ≫ x

attribute [reducible, instance] ModuleObj.homModule

/-- The commutative group scheme A over S is an abelian scheme: it is smooth and proper over S,
and multiplication by every m ≠ 0 is surjective. -/
class IsAbelianScheme extends AddObj A, Smooth A.hom, IsProper A.hom where
  /-- Multiplication by every natural number `m ≠ 0` is surjective. -/
  nsmul_surjective : ∀ m ≠ (0 : ℕ), Surjective (m • 𝟙 A).left

variable {A B T X Y : Over S} [AddObj A] [AddObj B]
  {R : outParam Type} [CommRing R] [ModuleObj R A] [ModuleObj R B] (c : R) (f : A ⟶ B)

/-- The morphism p : B → A makes B the base change of A along b : S' → S, and composing with p is
R-linear on T-points for every S'-scheme T. -/
structure IsGroupBaseChange {B : Over S'} [AddObj B] [ModuleObj R B]
    (p : (Over.map b).obj B ⟶ A) where
  /-- The square of `p`, `b` and the structure morphisms of `B` and `A` is cartesian. -/
  isPullback : IsPullback p.left B.hom A.hom b
  /-- For each `U` over `S'`, the map `u ↦ (Over.map b).map u ≫ p` from `U`-points of `B` to
  `(Over.map b).obj U`-points of `A` is `R`-linear. -/
  linear {U : Over S'} : IsLinearMap R (@(Over.map b).map U B · ≫ p)

/-! ### Homomorphisms -/

/-- The morphism f : A → B of commutative group objects is a homomorphism: composing with f is
additive on U-points for every U. -/
abbrev IsAdditive : Prop := IsAddMonHom f

/-- An isogeny is a homomorphism f : A → B that is finite, flat and surjective as a morphism of
schemes. -/
class abbrev IsIsogeny :=
  IsAddMonHom f, IsFinite f.left, Flat f.left, Surjective f.left

/-- The morphism f : A → B of R-module objects is a homomorphism that commutes with R:
multiplication by c on A followed by f equals c times f, for every c in R. -/
class IsLinear extends IsAddMonHom f where
  /-- Multiplication by `c` on `A` followed by `f` equals `c • f`. -/
  smul_id_comp (c : R) : (c • 𝟙 A) ≫ f = c • f

variable {f}

@[simp]
lemma IsLinear.smul_comp [hf : IsLinear f] (t : T ⟶ A) : (c • t : T ⟶ A) ≫ f = c • t ≫ f := by
  -- `c • t` is `t` followed by multiplication by `c` on `A`
  rw [show c • t = t ≫ (c • 𝟙 A) by rw [ModuleObj.comp_smul, Category.comp_id],
    Category.assoc, hf.smul_id_comp, ModuleObj.comp_smul]

-- For all importers, `simp` pulls scalar multiplication out of compositions
-- (`ModuleObj.comp_smul`).
attribute [simp] ModuleObj.comp_smul

/-- A morphism `f : A ⟶ B` of commutative group objects is a homomorphism if it is additive on the
universal pair of points, the two projections `fst A A` and `snd A A` of `A ⊗ A`. -/
lemma isAdditive_of_universal (h_univ : (fst A A + snd A A) ≫ f = fst A A ≫ f + snd A A ≫ f) :
    IsAdditive f := by
  constructor
  · -- At the point `(0, 0)` of `A ⊗ A`, `h_univ` reads `f 0 = f 0 + f 0`, so `f 0 = 0`.
    have h_at_zero : (0 : 𝟙_ (Over S) ⟶ A) ≫ f = 0 ≫ f + 0 ≫ f := by
      have h0 := lift (0 : 𝟙_ (Over S) ⟶ A) 0 ≫= h_univ
      rw [comp_add_assoc, comp_add, lift_fst, lift_snd, _root_.add_zero, ← Category.assoc, lift_fst,
        ← Category.assoc, lift_snd] at h0
      exact h0
    have h0 : (0 : 𝟙_ (Over S) ⟶ A) ≫ f = 0 :=
      add_left_cancel (a := (0 : 𝟙_ (Over S) ⟶ A) ≫ f)
        (by rw [_root_.add_zero]; exact h_at_zero.symm)
    have h_toUnit : toUnit (𝟙_ (Over S)) = 𝟙 (𝟙_ (Over S)) := toUnit_unique _ _
    rw [Hom.zero_def, Hom.zero_def, h_toUnit, Category.id_comp, Category.id_comp] at h0
    exact h0
  · -- The addition of `A` is `fst A A + snd A A`, so this is `h_univ`.
    rw [add_eq_add, add_eq_add, h_univ, comp_add, tensorHom_fst, tensorHom_snd]

/-- Every commutative group object is a `ℤ`-module object: the points form `ℤ`-modules through
integer multiples. -/
instance (priority := low) : ModuleObj ℤ A := ⟨fun a c x ↦ comp_zsmul a x c⟩

omit [ModuleObj R A] in
/-- A multiple `c • f` of a homomorphism `f` of commutative group objects is a homomorphism. -/
instance [IsAdditive f] : IsAdditive (c • f) := by
  apply isAdditive_of_universal
  rw [ModuleObj.comp_smul, ModuleObj.comp_smul, ModuleObj.comp_smul, add_comp, smul_add]

/-! ### Structures on the pullback, and properties of morphisms over the base -/

/-- The pull-back of a commutative group object A along b is a commutative group object. -/
@[irreducible]
instance pullbackAddObj : AddObj ((pullback b).obj A) where
  -- `↓` rewrites with `map_comp` backwards before `simp` visits the subterms
  add_comm := by simp [← LaxBraided.braided_assoc, ↓← map_comp, IsCommAddMonObj.add_comm]

/-- The pull-back along `b` of an `R`-module object `A` is an `R`-module object. -/
instance : ModuleObj R ((pullback b).obj A) where
  -- Transport the module structure on the points of `A` along the adjunction bijection.
  homModule _ :=
    AddEquiv.module _
      (.symm ⟨(mapPullbackAdj b).homEquiv .., fun x y ↦ by
        delta pullbackAddObj
        dsimp only [Equiv.toFun_as_coe]
        rw [homEquiv_unit, homEquiv_unit, homEquiv_unit, Functor.map_add', comp_add]⟩)
  comp_smul := by
    intro T' T a c x
    change a ≫ (mapPullbackAdj b).homEquiv T A (c • ((mapPullbackAdj b).homEquiv T A).symm x) =
      (mapPullbackAdj b).homEquiv T' A (c • ((mapPullbackAdj b).homEquiv T' A).symm (a ≫ x))
    rw [← homEquiv_naturality_left, ModuleObj.comp_smul, ← homEquiv_naturality_left_symm]

variable (c : Pic A.left) (x y : T ⟶ A) (f : X ⟶ Y) (z : 𝟙_ (Over S) ⟶ A)

/-- An isomorphism over `S` is an isomorphism of schemes. -/
instance [IsIso f] : IsIso f.left := map_isIso (forget S) f

/-- A morphism `f` over `S` from a proper `S`-scheme to a separated `S`-scheme is proper; `f.1`
is the underlying morphism of schemes `f.left`. -/
instance [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.1 := by
  -- `f.left ≫ Y.hom` is the proper structure morphism `X.hom`
  have h_comp : IsProper (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  exact IsProper.of_comp f.left Y.hom

/-- Smoothness of relative dimension `d` is stable under base change: if `f : X ⟶ S` is smooth of
relative dimension `d`, so is the projection `X ×_S Y ⟶ Y` for any `g : Y ⟶ S`. -/
instance {X Y S : Scheme} {d : ℕ} (f : X ⟶ S) (g : Y ⟶ S) [SmoothOfRelativeDimension d f] :
    SmoothOfRelativeDimension d (Limits.pullback.snd f g) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (.of_hasPullback f g)
    inferInstance

/-- The spectrum of an R-algebra B, as a scheme over Spec R. -/
abbrev specOver (R B : Type) [CommRing.{0} R] [CommRing B] [Algebra R B] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (ofHom (algebraMap R B)))

/-! ### Translations -/

/-- Translation by a section z of A over S: the S-morphism x ↦ x + z from A to itself. -/
@[simp]
abbrev translation : A ⟶ A := 𝟙 A + toUnit A ≫ z

/-- Translation by `z` is an isomorphism, with inverse the translation by `-z`. -/
instance : IsIso (translation z) where
  out := ⟨translation (-z),
    by rw [translation, translation, comp_add, Category.comp_id, ← Category.assoc,
        toUnit_unique ((𝟙 A + toUnit A ≫ z) ≫ toUnit A) (toUnit A), comp_neg, _root_.add_assoc,
        add_neg_cancel, _root_.add_zero],
    by rw [translation, translation, comp_add, Category.comp_id, ← Category.assoc,
        toUnit_unique ((𝟙 A + toUnit A ≫ (-z)) ≫ toUnit A) (toUnit A), comp_neg, _root_.add_assoc,
        neg_add_cancel, _root_.add_zero]⟩

namespace Pic

/-! ### Classes of line bundles at points -/

/-- For c in Pic A and a T-point x of A, the pull-back x^*c in Pic T. -/
def atPoint : Pic T.left := c.pull x.left

/-- For c in Pic A and T-points x, y of A, the class ⟨x, y⟩ = (x + y)^*c − x^*c − y^*c + 0^*c in
Pic T. -/
def pairing : Pic T.left := c.atPoint (x + y) - c.atPoint x - c.atPoint y + c.atPoint 0

/-- The parallelogram law for a class c in Pic A: (x+y)^*c + (x−y)^*c + 2·0^*c = 2(x^*c + y^*c)
in Pic T for all T-points x, y of A and all S-schemes T. -/
def ParallelogramLaw : Prop :=
  ∀ ⦃T : Over S⦄ (x y : T ⟶ A),
    c.atPoint (x + y) + c.atPoint (x - y) + 2 • c.atPoint 0 = 2 • (c.atPoint x + c.atPoint y)

end Pic

namespace Variety

open Pic

variable {R : CommRingCat} {A : Over (Spec R)} [IsLocalRing R] [AddObj A] {c : Pic A.left}

omit [AddObj A] in
/-- Over a local ring, a class pulls back to zero along a point that comes from a section. -/
@[simp]
lemma atPoint_toUnit_comp_eq_zero {T : Over (Spec R)} (z : 𝟙_ (Over (Spec R)) ⟶ A) :
    c.atPoint (toUnit T ≫ z) = 0 := by
  rw [Pic.atPoint, Over.comp_left, Pic.pull_comp, eq_zero_of_isLocalRing (c.pull z.left)]
  exact (Pic.pull (toUnit T).left).map_zero

@[simp]
lemma atPoint_zero {T : Over (Spec R)} : c.atPoint (T := T) 0 = 0 := atPoint_toUnit_comp_eq_zero _

end Variety

end New

end AbelianScheme

open CategoryTheory in
/-- For `b : X ⟶ Y` in a category, a commuting square `(Over.map b).map u ≫ p = p ≫ v` of morphisms
over `Y` gives the square `u.left ≫ p.left = p.left ≫ v.left` of the underlying morphisms. -/
private lemma CategoryTheory.Over.left_comp_left_eq_of_map_comp_eq {C : Type*} [Category C]
    {X Y : C} {b : X ⟶ Y} {U : Over X} {V : Over Y} {p : (Over.map b).obj U ⟶ V} {u : U ⟶ U}
    {v : V ⟶ V} (h_comm : (Over.map b).map u ≫ p = p ≫ v) : u.left ≫ p.left = p.left ≫ v.left :=
  congrArg CommaMorphism.left h_comm

/-!
## Points, sections and homomorphisms under base change

Throughout, `h : New.IsGroupBaseChange b p` says that `p` presents the group object `A'` over `S'`
as the base change of `A` along `b : S' ⟶ S`.
-/

namespace New.IsGroupBaseChange

open CategoryTheory MonoidalCategory Over CartesianMonoidalCategory

variable {S S' : AlgebraicGeometry.Scheme} {b : S' ⟶ S} {O : Type} [CommRing O] {A' : Over S'}
  {A : Over S} [AddObj (S := S') A'] [AddObj (S := S) A] [ModuleObj O A'] [ModuleObj O A]
  {p : (Over.map b).obj A' ⟶ A} (h : IsGroupBaseChange (A := A) (B := A') b p)

/-- For an O-compatible base change p : A' → A and an S'-scheme T, the O-linear bijection
x ↦ (Over.map b).map x ≫ p from T-points of A' over S' to T-points of A over S. -/
@[simps! -isSimp apply]
def pointEquiv {T : Over S'} : (T ⟶ A') ≃ₗ[O] ((Over.map b).obj T ⟶ A) :=
  -- the linear map `u ↦ (map b).map u ≫ p`, inverted by the universal property of the pull-back
  LinearEquiv.mk (h.linear (U := T)).mk' (fun u ↦ homMk (h.isPullback.lift u.left T.hom u.w))
    (fun x ↦ OverMorphism.ext (h.isPullback.hom_ext (h.isPullback.lift_fst _ _ _)
      ((h.isPullback.lift_snd _ _ _).trans x.w.symm)))
    (fun u ↦ OverMorphism.ext (h.isPullback.lift_fst u.left T.hom u.w))

/-- For a base change A' of A along b : S' → S, the O-linear map pulling sections of A over S
back to sections of A' over S'. -/
def pullSection : (𝟙_ (Over S) ⟶ A) →ₗ[O] 𝟙_ (Over S') ⟶ A' :=
  h.pointEquiv.symm.toLinearMap ∘ₗ
    ⟨⟨fun z ↦ toUnit ((Over.map b).obj (𝟙_ (Over S'))) ≫ z,
        comp_add (toUnit ((Over.map b).obj (𝟙_ (Over S'))))⟩,
      fun c z ↦ ModuleObj.comp_smul _ c z⟩

@[reassoc]
lemma pullSection_comp (z : 𝟙_ (Over S) ⟶ A) : (h.pullSection z).left ≫ p.left = b ≫ z.left := by
  have h_u : (toUnit ((Over.map b).obj (𝟙_ (Over S')))).left = b :=
    ((toUnit ((Over.map b).obj (𝟙_ (Over S')))).w.symm.trans (Category.comp_id _)).symm
  refine (h.isPullback.lift_fst _ _ _).trans ?_
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Over.comp_left, h_u]

/-- For a base change p : A' → A, a line bundle N on A and a T-point x of A', the pull-back of
the class of p*N along x equals the pull-back of the class of N along the point p∘x of A. -/
lemma atPoint_picClass_pull {T : Over S'} {ι : Type} {N : LineBundle A.left ι} (x : T ⟶ A') :
    Pic.atPoint (A := A') (T := T) (N.pull p.left).picClass x =
      (LineBundle.picClass (ι := ι) N).atPoint (h.pointEquiv x) := by
  rw [Pic.atPoint, Pic.atPoint, h.pointEquiv_apply, ← Pic.pull_picClass, ← Pic.pull_comp]
  rfl

/-- `p` commutes with multiplication by `m` in `O` on `A'` and on `A`. -/
lemma smul_id_comp (h : IsGroupBaseChange (A := A) (B := A') b p) (m : O) :
    (m • 𝟙 A').left ≫ p.left = p.left ≫ (m • 𝟙 A).left := by
  -- the map `u ↦ (map b).map u ≫ p` is linear; apply this to `m • 𝟙 A'`
  have h_comm : (map b).map (m • 𝟙 A') ≫ p = p ≫ (m • 𝟙 A) := by
    rw [h.linear.map_smul m (𝟙 A'), CategoryTheory.Functor.map_id, Category.id_comp,
      ModuleObj.comp_smul, Category.comp_id]
  exact Over.left_comp_left_eq_of_map_comp_eq h_comm

/-- `p` commutes with multiplication by a natural number `m` on `A'` and on `A`. -/
lemma nsmul_id_comp (h : IsGroupBaseChange (A := A) (B := A') b p) (m : ℕ) :
    (m • 𝟙 A').left ≫ p.left = p.left ≫ (m • 𝟙 A).left :=
  mod_cast h.smul_id_comp m

/-- `p` carries translation by the pulled-back section `New.IsGroupBaseChange.pullSection` of `z` to
translation by `z`. -/
lemma translation_comp (h : IsGroupBaseChange (A := A) (B := A') b p) (z : 𝟙_ (Over S) ⟶ A) :
    (translation (h.pullSection z)).left ≫ p.left = p.left ≫ (translation z).left := by
  -- `translation` adds a constant section to `𝟙`, and the map `u ↦ (map b).map u ≫ p` is additive
  have h_sec : h.pointEquiv (h.pullSection z) =
      toUnit ((Over.map b).obj (𝟙_ (Over S'))) ≫ z :=
    h.pointEquiv.apply_symm_apply _
  have h_comm : (map b).map (New.translation (h.pullSection z)) ≫ p = p ≫ New.translation z := by
    rw [New.translation, New.translation, comp_add, Category.comp_id, h.linear.map_add,
      CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, ← h.pointEquiv_apply, h_sec, ← Category.assoc,
      toUnit_unique ((map b).map (toUnit A') ≫ toUnit _) (p ≫ toUnit A), Category.assoc]
  exact Over.left_comp_left_eq_of_map_comp_eq h_comm

/-- Let `A'` be a base change of `A` along `b` and `B'` one of `B` along `c`, with `b c : S' ⟶ S`,
and let `F : map c ⟶ map b` be a natural map. An `O`-linear homomorphism `χ : A ⟶ B` induces
`ψ : A' ⟶ B'` such that (a) read through `pointEquiv`, the `T`-point `u ≫ ψ` is `F`, then `u`,
then `χ`; (b) `ψ` is additive and `O`-linear; (c) `ψ` sends the pull-back of a section `z` to the
pull-back of `z ≫ χ`. -/
lemma exists_hom_baseChange (h : IsGroupBaseChange (A := A) (B := A') b p) {c : S' ⟶ S}
    {B' : Over S'} {B : Over S} [AddObj B'] [AddObj B] [ModuleObj O B'] [ModuleObj O B]
    {q : (Over.map c).obj B' ⟶ B} (hB : IsGroupBaseChange c q)
    (F : Over.map c ⟶ Over.map b) (χ : A ⟶ B) [IsLinear χ] :
    ∃ ψ : A' ⟶ B',
      (∀ {T : Over S'} (u : T ⟶ A'), hB.pointEquiv (u ≫ ψ) = F.app T ≫ h.pointEquiv u ≫ χ) ∧
      IsLinear ψ ∧
      ∀ z : 𝟙_ (Over S) ⟶ A, h.pullSection z ≫ ψ = hB.pullSection (z ≫ χ) := by
  -- `ψ` is the point of `B'` that corresponds to `F.app A' ≫ p ≫ χ`. Each property is checked after
  -- applying the injective linear map `hB.pointEquiv`, where `hψ` reduces it to a property of `χ`.
  obtain ⟨ψ, h_def⟩ := hB.pointEquiv.surjective (F.app A' ≫ p ≫ χ)
  -- (a), by naturality of `F`
  have hψ {T : Over S'} (u : T ⟶ A') :
      hB.pointEquiv (u ≫ ψ) = F.app T ≫ h.pointEquiv u ≫ χ := by
    rw [hB.pointEquiv_apply, CategoryTheory.Functor.map_comp, Category.assoc,
      ← hB.pointEquiv_apply, h_def, NatTrans.naturality_assoc, h.pointEquiv_apply, Category.assoc]
  have h_universal : (fst A' A' + snd A' A') ≫ ψ = fst A' A' ≫ ψ + snd A' A' ≫ ψ := by
    apply hB.pointEquiv.injective
    rw [LinearEquiv.map_add, hψ, hψ, hψ, LinearEquiv.map_add, add_comp, comp_add]
  have h_add : IsAdditive ψ := isAdditive_of_universal h_universal
  refine ⟨ψ, hψ, { h_add with smul_id_comp := fun m ↦ ?_ }, fun z ↦ ?_⟩
  · -- (b): `O`-linearity of `ψ`, from that of `h.pointEquiv` and of `χ`
    apply hB.pointEquiv.injective
    rw [hψ, LinearEquiv.map_smul, IsLinear.smul_comp, ModuleObj.comp_smul, ← hψ,
      Category.id_comp, LinearEquiv.map_smul]
  · -- (c): after `hB.pointEquiv`, both sides are the constant point `z ≫ χ`
    apply hB.pointEquiv.injective
    have h_secA : h.pointEquiv (h.pullSection z) =
        toUnit ((Over.map b).obj (𝟙_ (Over S'))) ≫ z :=
      h.pointEquiv.apply_symm_apply _
    have h_secB : hB.pointEquiv (hB.pullSection (z ≫ χ)) =
        toUnit ((Over.map c).obj (𝟙_ (Over S'))) ≫ z ≫ χ :=
      hB.pointEquiv.apply_symm_apply _
    rw [hψ, h_secA, h_secB, ← Category.assoc, ← Category.assoc,
      toUnit_unique (F.app (𝟙_ (Over S')) ≫ toUnit _) (toUnit _), Category.assoc]

end New.IsGroupBaseChange

/-!
## Kernels of finite homomorphisms

`New.AddObj B` makes `B` a commutative group object with zero section `ζ[B]`, and `New.specOver R S`
is `Spec S` as a scheme over `Spec R`.
-/

section KernelRing

open CategoryTheory AlgebraicGeometry Spec Over MorphismProperty AddMonObj

namespace New.Variety

variable {R : Type} [CommRing R] {A B : Over (Spec ⟨R⟩)} [AddObj B] {f : A ⟶ B}

omit [AddObj B] in
/-- If `A` is locally of finite presentation over `Spec R` and `B` is locally of finite type over
`Spec R`, then every morphism `f : A ⟶ B` over `Spec R` is locally of finite presentation. -/
@[stacks 02FV "first assertion, over an affine base"]
lemma locallyOfFinitePresentation_left [hB : LocallyOfFiniteType B.hom]
    [h : LocallyOfFinitePresentation A.hom] :
    LocallyOfFinitePresentation f.left := by
  -- On affine opens `V ≤ f ⁻¹ U`: `Γ(V)` is finitely presented and `Γ(U)` of finite type over `R`,
  -- so `Γ(V)` is finitely presented over `Γ(U)`.
  rw [← f.w] at h
  refine ⟨fun {U} hU {V} hV hVU ↦ ?_⟩
  have hV_pres : ((f.left ≫ B.hom).appLE ⊤ V le_top).hom.FinitePresentation :=
    LocallyOfFinitePresentation.finitePresentation_appLE (f.left ≫ B.hom) (isAffineOpen_top _) hV
      le_top
  have hU_type : (B.hom.appLE ⊤ U le_top).hom.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE B.hom (isAffineOpen_top _) hU le_top
  rw [← f.left.appLE_comp_appLE B.hom ⊤ U V le_top hVU] at hV_pres
  exact hV_pres.of_comp_finiteType _ hU_type

/-- The pull-back of an affine morphism `f` along a point `Spec C ⟶ Y` is `Spec` of a ring map
`C ⟶ P`. -/
lemma exists_isPullback_SpecMap {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom.{0} f] {C : CommRingCat}
    (i : Spec C ⟶ Y) :
    ∃ (P : CommRingCat) (φ : C ⟶ P) (j : Spec P ⟶ X),
      IsPullback j (Spec.map (R := C) (S := P) φ) f i := by
  -- The pull-back is affine over `Spec C`, so it is `Spec` of its ring of global sections.
  let e : Spec Γ(Limits.pullback f i, ⊤) ≅ Limits.pullback f i := (Scheme.isoSpec _).symm
  refine ⟨Γ(Limits.pullback f i, ⊤), Spec.preimage (e.hom ≫ Limits.pullback.snd f i),
    e.hom ≫ Limits.pullback.fst f i, ?_⟩
  exact .of_iso_pullback
    ⟨by rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Spec.map_preimage]⟩
    e rfl (Spec.map_preimage _).symm

open MonoidalCategory in
/-- A morphism `f : A ⟶ B` over `Spec R` is zero exactly when, as a morphism of schemes, it factors
through the zero section `ζ[B]` of `B`. -/
lemma eq_zero_iff_factors_zero_section :
    f = 0 ↔ ∃ l : A.left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left, l ≫ ζ[B].left = f.left := by
  have h_u : (CartesianMonoidalCategory.toUnit A).left = A.hom :=
    (Category.comp_id _).symm.trans (CartesianMonoidalCategory.toUnit A).w
  constructor
  · -- `0 : A ⟶ B` is the structure morphism of `A` followed by the zero section
    intro hf
    refine ⟨A.hom, ?_⟩
    rw [hf, Hom.zero_def, Over.comp_left, h_u]
  · -- `l` is the structure morphism of `A`, since `ζ[B]` is a section of `B`
    rintro ⟨l, hl⟩
    apply OverMorphism.ext
    rw [Hom.zero_def, Over.comp_left, h_u, ← hl]
    have hl_eq : l = A.hom := by
      rw [← Category.comp_id l]
      change l ≫ (𝟙_ (Over (Spec (CommRingCat.of R)))).hom = A.hom
      rw [← Over.w ζ[B], ← Category.assoc, hl, f.w]
    rw [hl_eq]

/-- `ι : Spec S ⟶ A` is the kernel of `f : A ⟶ B` over `Spec R`, and `S` is finite over `R`: `ι` is
a closed immersion killed by `f`, through which every point of `A` killed by `f` factors; `S` is
flat over `R` if `f` is flat. -/
structure IsFiniteKernelRing (f : A ⟶ B) (S : CommAlgCat R) (ι : specOver R S ⟶ A) : Prop where
  /-- `S` is a finite `R`-module. -/
  finite : Module.Finite R S
  /-- `S` is flat over `R` if `f` is flat. -/
  flat : ∀ [Flat f.left], Module.Flat R S
  /-- `ι` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι.left
  /-- `ι` is killed by `f`. -/
  comp_eq_zero : ι ≫ f = 0
  /-- Every point of `A` killed by `f` factors through `ι`. -/
  exists_comp_eq : ∀ ⦃T : Over (Spec (CommRingCat.of R))⦄ (y : T ⟶ A),
    y ≫ f = 0 → ∃ z : T ⟶ specOver R S, z ≫ ι = y

variable [IsSeparated B.hom]

/-- The zero section of a separated commutative group scheme is a closed immersion. -/
instance : IsClosedImmersion ζ[B].left := by
  -- The zero section is a section of the separated morphism `B.hom`.
  have h_id : IsClosedImmersion (ζ[B].left ≫ B.hom) := by
    rw [Over.w ζ[B]]
    exact (inferInstance : IsClosedImmersion (𝟙 (Spec (CommRingCat.of R))))
  -- `MorphismProperty.of_postcomp` takes the property `@IsClosedImmersion` as its first argument
  exact of_postcomp @IsClosedImmersion ζ[B].left B.hom (inferInstance : IsSeparated B.hom) h_id

/-- Let `B` be a separated commutative group scheme over `R` and `f : A ⟶ B` a finite morphism over
`R`. The fibre of `f` over the zero section is affine: it is `Spec S` for a finite `R`-algebra `S`,
flat over `R` if `f` is flat (`New.Variety.IsFiniteKernelRing`). -/
lemma exists_finite_kernel_ring (hf : IsFinite f.left) :
    ∃ (S : CommAlgCat R) (ι : specOver R S ⟶ A), IsFiniteKernelRing f S ι := by
  -- The kernel is the pull-back `Spec P` of the zero section along the affine morphism `f`;
  -- finiteness, flatness and being a closed immersion are stable under base change.
  obtain ⟨P, φ, i, h_pb⟩ := exists_isPullback_SpecMap f.left ζ[B].left
  let : Algebra R P := φ.hom.toAlgebra
  -- finiteness and flatness
  have h_finite : Module.Finite R P := (IsFinite.SpecMap_iff φ).mp (of_isPullback h_pb hf)
  have h_flat : ∀ [Flat f.left], Module.Flat R P :=
    fun [Flat f.left] ↦ Flat.SpecMap_iff.mp (of_isPullback h_pb inferInstance)
  -- the closed immersion `ι`, killed by `f`
  have h_over : i ≫ A.hom = Spec.map φ := by
    rw [← Over.w f, h_pb.w_assoc B.hom, Over.w ζ[B]]
    exact Category.comp_id _
  let ι : specOver R P ⟶ A := homMk i h_over
  have h_closed : IsClosedImmersion ι.left := of_isPullback h_pb.flip inferInstance
  have h_zero : ι ≫ f = 0 := eq_zero_iff_factors_zero_section.mpr ⟨Spec.map φ, h_pb.w.symm⟩
  refine ⟨.of R P, ι, h_finite, h_flat, h_closed, h_zero, fun T y hy ↦ ?_⟩
  -- a point `y` killed by `f` and the structure morphism of `T` map to the pull-back square
  have hy_left : y.left ≫ f.left = T.hom ≫ ζ[B].left := by
    have hyl : (y ≫ f).left = (0 : T ⟶ B).left := congrArg CommaMorphism.left hy
    rw [Over.comp_left, Hom.zero_def, Over.comp_left] at hyl
    have h_u : (CartesianMonoidalCategory.toUnit T).left = T.hom :=
      (Category.comp_id _).symm.trans (CartesianMonoidalCategory.toUnit T).w
    rwa [h_u] at hyl
  exact ⟨homMk (h_pb.lift y.left T.hom hy_left) (h_pb.lift_snd y.left T.hom hy_left),
    OverMorphism.ext (h_pb.lift_fst y.left T.hom hy_left)⟩

end New.Variety

end KernelRing

/-!
## Global functions on a base change of an abelian variety

`New.HasConstFunctions s` says that global sections of `X`, viewed as functions on ring-valued
points (`New.PointFn.ofSection`), are constant on the fibres of `s`.
-/

section ConstantFunctions

open CategoryTheory AlgebraicGeometry New.PointFn Scheme.Hom AddMonObj

/-- For s : X → S, every function regular on all of X takes equal values at two ring-valued
points of X with the same image under s. -/
def New.HasConstFunctions {X S : Scheme} (s : X ⟶ S) : Prop :=
  ∀ (c : Γ(X, ⊤)) (B : CommRingCat) (x y : Spec B ⟶ X),
    x ≫ s = y ≫ s → ofSection c B x = ofSection c B y

/-- Let A be an integral abelian scheme over a field k and X = A ×_k Spec C. A function regular on
all of X takes equal values at any two ring-valued points with the same image in Spec C. -/
lemma New.Variety.hasConstFunctions_of_isPullback {k : Type} [Field k]
    {A : Over (Spec (CommRingCat.of k))}
    [IsAbelianScheme A] [IsIntegral A.left] {X : Scheme} {C : CommRingCat} {p : X ⟶ A.left}
    {s : X ⟶ Spec C} {q : Spec C ⟶ Spec (CommRingCat.of k)}
    (h_pullback : IsPullback (P := X) (Y := Spec C) p s A.hom q) :
    HasConstFunctions s := by
  -- Flat base change gives `Γ(X) = Γ(A) ⊗[k] C`, and `k → Γ(A)` is onto; so `C → Γ(X)` is an
  -- epimorphism, and evaluation at a point of `X` is determined by its image in `Spec C`.
  intro f B x y hxy
  have h_top : (⊤ : X.Opens) = p ⁻¹ᵁ ⊤ ⊓ s ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top, inf_idem]
  have h_pushout : IsPushout (A.hom.appLE ⊤ ⊤ le_top) (q.appLE ⊤ ⊤ le_top) (p.appLE ⊤ ⊤ le_top)
      (s.appLE ⊤ ⊤ le_top) :=
    (isIso_pushoutSection_iff h_pullback le_top le_top h_top).mp <|
      isIso_pushoutSection_of_isQuasiSeparated_of_flat_right h_pullback le_top le_top h_top
        (isAffineOpen_top _) (isAffineOpen_top _)
        (isCompact_preimage A.hom (U := ⊤) (isAffineOpen_top _).isCompact)
        (isQuasiSeparated_preimage A.hom (U := ⊤) isQuasiSeparated_univ)
  -- `Γ(A)` is a field, so evaluation at the zero section is injective; it is a retraction of
  -- `k → Γ(A)`, which is therefore surjective.
  let _ : Field Γ(A.left, ⊤) := (isField_of_universallyClosed _ A.hom).toField
  have h_inj : Function.Injective ζ[A].left.appTop :=
    RingHom.injective (S := Γ(Spec (.of k), ⊤)) ζ[A].left.appTop.hom
  have h_sec : Function.LeftInverse ζ[A].left.appTop A.hom.appTop := fun a ↦ by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show ζ[A].left ≫ A.hom = 𝟙 _ from Over.w ζ[A], Scheme.Hom.id_appTop]
    rfl
  have h_epi : Epi (s.appLE ⊤ ⊤ le_top) := h_pushout.epi_inr_of_epi <| by
    rw [show A.hom.appLE ⊤ ⊤ le_top = A.hom.appTop from appLE_eq_app A.hom]
    exact ConcreteCategory.epi_of_surjective _ (h_sec.rightInverse_of_injective h_inj).surjective
  -- Both evaluations agree on the sections that come from `Spec C`, since `x ≫ s = y ≫ s` (`hxy`).
  have h_agree : s.appLE ⊤ ⊤ le_top ≫ evalSection x landsIn_top =
      s.appLE ⊤ ⊤ le_top ≫ evalSection y landsIn_top := by
    dsimp only [evalSection]
    rw [appLE_comp_appLE_assoc x s ⊤ ⊤ ⊤ le_top landsIn_top,
      appLE_comp_appLE_assoc y s ⊤ ⊤ ⊤ le_top landsIn_top, hxy]
  rw [ofSection_eq landsIn_top, ofSection_eq landsIn_top, h_epi.left_cancellation _ _ h_agree]

end ConstantFunctions

end
