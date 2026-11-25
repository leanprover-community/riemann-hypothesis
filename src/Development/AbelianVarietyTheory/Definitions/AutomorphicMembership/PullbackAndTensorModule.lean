module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullRigIsSymmetric
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical, Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry", "h": "module\n\npublic import Mathlib.NumberTheory.NumberField.CMField\npublic import Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct
open NumberField

namespace GlobalTheory

abbrev SesqForm (R M : Type*) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

structure HermForm (R M : Type*) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M] where

  toSesq : SesqForm R M
  star_apply' : ∀ x y, star (toSesq x y) = toSesq y x

namespace HermForm

section Ring

variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

instance : FunLike (HermForm R M) M (M →ₗ⋆[R] R) where
  coe h := h.toSesq
  coe_injective f g H := by
    cases f; cases g; congr; exact DFunLike.coe_injective H

instance : LinearMapClass (HermForm R M) R M (M →ₗ⋆[R] R) where
  map_add h := h.toSesq.map_add
  map_smulₛₗ h := h.toSesq.map_smul

variable (h : HermForm R M)

def ofFun (f : M → M → R) (add_left : ∀ x y z, f (x + y) z = f x z + f y z)
    (smul_left : ∀ (a : R) x y, f (a • x) y = a * f x y)
    (star_symm : ∀ x y, star (f x y) = f y x) : HermForm R M where
  toSesq := LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) f add_left smul_left
    (fun x y z => by rw [← star_symm, add_left, star_add, star_symm, star_symm])
    (fun a x y => by rw [← star_symm, smul_left, star_mul', star_symm]; rfl)
  star_apply' := star_symm

def Nondegenerate : Prop := h.toSesq.Nondegenerate

variable {h}

theorem Nondegenerate.eq_zero_left (H : h.Nondegenerate) {x : M} (hx : ∀ y, h x y = 0) : x = 0 :=
  H.1 x hx

structure IsometryEquiv (h₁ : HermForm R M) (h₂ : HermForm R N) extends M ≃ₗ[R] N where
  map_app' : ∀ x y, h₂ (toFun x) (toFun y) = h₁ x y

def Isometric (h₁ : HermForm R M) (h₂ : HermForm R N) : Prop := Nonempty (h₁.IsometryEquiv h₂)

namespace IsometryEquiv

variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

instance : EquivLike (h₁.IsometryEquiv h₂) M N where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

instance : LinearEquivClass (h₁.IsometryEquiv h₂) R M N where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

@[symm] def symm (f : h₁.IsometryEquiv h₂) : h₂.IsometryEquiv h₁ :=
  ⟨f.toLinearEquiv.symm, fun x y => by
    rw [← f.map_app]
    exact congrArg₂ (fun a b => h₂ a b) (f.toLinearEquiv.apply_symm_apply x)
      (f.toLinearEquiv.apply_symm_apply y)⟩

@[trans] def trans (f : h₁.IsometryEquiv h₂) (g : h₂.IsometryEquiv h₃) : h₁.IsometryEquiv h₃ :=
  ⟨f.toLinearEquiv.trans g.toLinearEquiv, fun x y => (g.map_app _ _).trans (f.map_app x y)⟩

end IsometryEquiv

namespace Isometric

variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

end Isometric

def unitaryGroup (h : HermForm R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' _ _ := rfl
  mul_mem' hg hg' x y := (hg _ _).trans (hg' x y)
  inv_mem' {g} hg x y := by
    rw [← hg]
    exact congrArg₂ (fun a b => h a b) (g.apply_symm_apply x) (g.apply_symm_apply y)

namespace unitaryGroup

end unitaryGroup

end Ring

section Field

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}

end Field

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : HermForm ℂ V)

variable {h}

end Complex

end HermForm

universe u v

structure HermModule (R : Type u) [CommRing R] [StarRing R] where

  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]

  form : HermForm R carrier

attribute [instance] HermModule.addCommGroup HermModule.module

structure HermSpace (K : Type u) [Field K] [StarRing K] where

  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]
  [finite : FiniteDimensional K carrier]

  form : HermForm K carrier
  nondegenerate : form.Nondegenerate

attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite

class IsStarFixed (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E] :
    Prop where
  star_algebraMap : ∀ a : F, star (algebraMap F E a) = algebraMap F E a

attribute [simp] IsStarFixed.star_algebraMap

section IsStarFixed

variable (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E]

variable [IsStarFixed F E]

variable {F E}

end IsStarFixed

def StarTensor (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E]
    [Algebra F A] : Type _ := E ⊗[F] A

namespace StarTensor

section NoStar

variable (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]

variable {F E A}

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra F B] [Algebra F C]

end NoStar

section Star

variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]

variable {B : Type*} [CommRing B] [Algebra F B]

end Star

end StarTensor

section RingOfIntegers

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

end RingOfIntegers

section CM

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

variable {E}

noncomputable instance : StarRing (𝓞 E) where
  star := IsCMField.ringOfIntegersComplexConj E
  star_involutive x := RingOfIntegers.ext (star_star (x : E))
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y

variable (E) in
abbrev CMTensor (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A] : Type _ :=
  StarTensor (maximalRealSubfield E) E A

namespace CMTensor

variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]

end CMTensor

end CM

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullRigIsSymmetric\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry\npublic import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple\npublic import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian\npublic import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfRetract\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB GlobalTheory.HomComb
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

open ReciprocityTheory.ChartRestriction.G.Out

section Transport

variable {X X' W W' Y Y' Y₀ Y₀' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Φ : W' ⟶ W}
  {J K : Type} [Fintype J] [Fintype K] {u : J → (W ⟶ X)} {u' : J → (W' ⟶ X')}

def combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) (w : LB.Iso L' (L.pull F)) :
    LB.Iso (LB.LinComb L' u' δ) ((LB.LinComb L u δ).pull Φ) where
  s p := ∏ i, res (U := u' i ⁻¹ᵁ ((L.pull F).U (fun _ => p.1 ⟨⟩ i) ⊓ L'.U (p.2 i)))
    (V := ((LB.LinComb L u δ).pull Φ).U p.1 ⊓ (LB.LinComb L' u' δ).U p.2)
    (fun y hy => ⟨mem_pull.2 (mem_of_comm (hu i).symm y (Set.mem_iInter.1 (mem_pull.1 hy.1) i)),
      Set.mem_iInter.1 hy.2 i⟩) (pullU (u' i) _ (w.s (fun _ => p.1 ⟨⟩ i, p.2 i))) ^ δ i

end Transport

variable {S S' : Scheme.{0}} {G A : Over S} {G' A' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  [GrpObj G'] [IsCommMonObj G'] [GrpObj A'] [IsCommMonObj A'] {J : Type} [Fintype J]

end GlobalTheory.HomComb

namespace GlobalTheory.HermTensor

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

variable {O : Type} [CommRing O] [StarRing O] {M : Type} [AddCommGroup M] [Module O M]
  {a : OAct O G} {b : OAct O A} (t : IsTensor A b G a M) (P : Summand O M) (h : HermForm O M)

def gen (i : Fin P.n) : M := P.proj (Pi.single i 1)

def gram (i j : Fin P.n) : O := h (gen P j) (gen P i)

def crd (i : Fin P.n) : A ⟶ G := t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)

instance isMonHom_crd (i : Fin P.n) : IsMonHom (crd t P i) := IsTensor.isMonHom_mapLeft _ _ _

abbrev BIx (n : ℕ) : Type := (Fin n × Fin n) × ULift.{0} (Finset (Fin 2))

def biExp (n : ℕ) (q : BIx n) : ℤ := (-1) ^ (2 - q.2.down.card)

def biMap (x z : T ⟶ A) (q : BIx P.n) : T ⟶ G :=
  psum G ![x ≫ crd t P q.1.1, z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)] q.2.down

instance isMonHom_biMap [GrpObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z] (q : BIx P.n) :
    IsMonHom (biMap t P h x z q) :=
  isMonHom_psum _ (fun i => by
    have := a.hom
    fin_cases i
    · exact inferInstanceAs (IsMonHom (x ≫ crd t P q.1.1))
    · exact inferInstanceAs (IsMonHom (z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)))) _

def biLB (L : LB G.left) (x z : T ⟶ A) : LB T.left :=
  LB.LinComb L (fun q => (biMap t P h x z q).left) (biExp P.n)

def bi (c : Pic G.left) (x z : T ⟶ A) : Pic T.left :=
  ∑ i, ∑ j, lam c (x ≫ crd t P i) (z ≫ crd t P j ≫ a.act (gram P h i j))

def IsAdj (a : OAct O G) (L : LB G.left) : Prop :=
  ∀ c, LBIso (cubeLB G ![fst G G ≫ a.act c, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a.act (star c)] L)

section Rigid

variable [GrpObj T] [IsCommMonObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z]

def biRig (L : RigLB G) : RigLB T := combRig (biMap t P h x z) (biExp P.n) L

def biCub {L : RigLB G} (c : CubicalStr G L) : CubicalStr T (biRig t P h x z L) := combCub _ _ c

end Rigid

def poi (L : RigLB G) : RigLB (A ⊗ A) := biRig t P h (fst A A) (snd A A) L

def theta (w : O) (L : RigLB G) : RigLB A := haveI := b.hom w; biRig t P h (𝟙 A) (b.act w) L

def thetaCub (w : O) {L : RigLB G} (c : CubicalStr G L) : CubicalStr A (theta t P h w L) :=
  haveI := b.hom w; biCub t P h (𝟙 A) (b.act w) c

end GlobalTheory.HermTensor
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical\npublic import Formalism.LocalToGlobal.ProjectiveLattices.ThShort\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

structure Unim (E : Type) [Field E] [NumberField E] [IsCMField E] : Type where

  n : ℕ

  form : HermForm E (Fin n → E)
  pos : ∀ (σ : E →+* ℂ) (x : Fin n → E), x ≠ 0 → 0 < (σ (form x x)).re

  L : Submodule (𝓞 E) (Fin n → E)
  isLattice : Submodule.IsFullLattice E L
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular form.toSesq.flip L

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Unim

variable (Λ : Unim E)

def gramE : Matrix (Fin Λ.n) (Fin Λ.n) E := fun i j => Λ.form (Pi.single i 1) (Pi.single j 1)

instance : Module.Finite (𝓞 E) Λ.L := Module.Finite.iff_fg.2 Λ.isLattice.fg

instance : Module.Projective (𝓞 E) Λ.L :=
  have : Module.FinitePresentation (𝓞 E) Λ.L := Module.finitePresentation_of_finite _ _
  Module.Flat.projective_of_finitePresentation

def hInt : HermForm (𝓞 E) Λ.L :=
  HermForm.ofFun (fun x y => ⟨Λ.form x y, Λ.isIntegral_form x y⟩)
    (fun x y z => RingOfIntegers.ext (Λ.form.add_left x y z))
    (fun c x y => RingOfIntegers.ext (Λ.form.smul_left (c : E) x y))
    (fun x y => RingOfIntegers.ext (Λ.form.star_apply x y))

def pres : Summand (𝓞 E) Λ.L := Summand.choose _ _

section Group

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (a : OAct (𝓞 E) G)

abbrev obj : Over X := Λ.pres.obj a

abbrev act : OAct (𝓞 E) (Λ.obj a) := Λ.pres.act a

abbrev isTensor : IsTensor (Λ.obj a) (Λ.act a) G a Λ.L := Λ.pres.isTensor a

end Group

variable (E) in
def stdForm (n : ℕ) : HermForm E (Fin n → E) :=
  HermForm.ofFun (fun x y => ∑ i, x i * star (y i)) (fun x y z => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, _root_.mul_assoc]) (fun x y => by simp [mul_comm])

def ofGenLat {n : ℕ} (Γ : Formalism.L2.Pj.GenLat E n) (hL : Submodule.IsFullLattice E Γ.La) (hU : Γ.Unimod) : Unim E where
  n := n
  form := stdForm E n
  pos := stdForm_pos
  L := Γ.La
  isLattice := hL
  unimod := by
    ext x
    rw [hU x]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    refine forall₂_congr fun y _ => ?_
    have e : ∑ j, IsCMField.complexConj E (x j) * y j = star (stdForm E n x y) := by
      rw [HermForm.star_apply, stdForm_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    exact ⟨fun ⟨c, hc⟩ => ⟨star c, congrArg star hc⟩, fun ⟨c, hc⟩ => ⟨star c, (congrArg star hc).trans (star_star _)⟩⟩

omit [NumberField E] [IsCMField E] in
theorem mem_stdLat {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = x i := by
  simp [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in
theorem single_mem_stdLat {n : ℕ} (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n :=
  (mem_stdLat _).2 fun j => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
    by_cases h : j = i <;> simp [h]⟩

variable (E) in
def stdEquiv (n : ℕ) : Formalism.L2.Pj.stdLat E n ≃ₗ[𝓞 E] (Fin n → 𝓞 E) where
  toFun x i := ⟨x.1 i, by obtain ⟨c, hc⟩ := (mem_stdLat _).1 x.2 i; exact hc ▸ c.isIntegral_coe⟩
  invFun v := ⟨fun i => algebraMap (𝓞 E) E (v i), (mem_stdLat _).2 fun i => ⟨v i, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField E] [IsCMField E] in
theorem isLattice_stdLat (n : ℕ) : Submodule.IsFullLattice E (Formalism.L2.Pj.stdLat E n) := by
  have hspan : Submodule.span E (Formalism.L2.Pj.stdLat E n : Set (Fin n → E)) = ⊤ :=
    eq_top_iff.2 fun x _ => by
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat i))
  refine { toIsLattice := ?_, span_eq_top := hspan }
  refine (Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank E _).2 ⟨?_, ?_⟩
  · exact Module.Finite.iff_fg.1 (Module.Finite.equiv (stdEquiv E n).symm)
  · rw [hspan, finrank_top, (stdEquiv E n).finrank_eq, Module.finrank_fin_fun, Module.finrank_fin_fun]

variable (E) in
def std (n : ℕ) : Unim E := ofGenLat ⟨Formalism.L2.Pj.stdLat E n⟩ (isLattice_stdLat n) (unimod_stdLat n)

end Unim

variable {H : Host E} {X X' : Scheme.{0}}

theorem bar_eq_star (H : Host E) (c : 𝓞 E) : H.bar c = star c := RingOfIntegers.ext (H.bar_eq c)

def sabOfTensor (t : SAB H X) {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [Module.Projective (𝓞 E) M] {A : Over X} [GrpObj A] [IsCommMonObj A] {b : OAct (𝓞 E) A}
    (T : IsTensor A b t.G t.act M) (P : Summand (𝓞 E) M) (h : HermForm (𝓞 E) M) : SAB H X where
  G := A
  semi := isSemiAbelian_tensor T t.semi
  act := b
  PP := theta T P h H.w0 t.PP
  cub := thetaCub T P h H.w0 t.cub
  sym := theta_isSymmetric T P h H.w0 t.cub t.sym
  adj c := bar_eq_star H c ▸ theta_isAdj T P h t.cub (isAdj_sab t) (halfUnit_add_star H) c
  prim := theta_prim T P h t.cub (isAdj_sab t) (halfUnit_add_star H)

def tens (t : SAB H X) (Λ : Unim E) : SAB H X := sabOfTensor t (Λ.pres.isTensor t.act) Λ.pres Λ.hInt

namespace tens

variable (t : SAB H X) (Λ : Unim E)

def isTensor : IsTensor (tens t Λ).G (tens t Λ).act t.G t.act Λ.L := Λ.pres.isTensor t.act

def poi : RigLB ((tens t Λ).G ⊗ (tens t Λ).G) := HermTensor.poi (isTensor t Λ) Λ.pres Λ.hInt t.PP

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

def map : SABMap (tens t' Λ) (tens t Λ) f :=
  have H := ((isTensor t Λ).exists_isLinearPullback (isTensor t' Λ) (isLinearPullback_sabMap m)).choose_spec
  { cm := cubeMapOf H.1.1
    cart := H.1.1
    base := rfl
    act := H.1.2
    lin := thetaCub_isPullCubical (isTensor t Λ) Λ.pres Λ.hInt (isTensor t' Λ) (isLinearPullback_sabMap m) H.1 H.2 _
      m.cm rfl m.base m.lin }

end tens

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def uniTrue (ct : At S κ p) : UniSt ct where
  Unim := Unim D.host.E
  latStd := Unim.std D.host.E

end Record

end GlobalTheory.LocM
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule =====
