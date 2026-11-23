module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.QCoh

namespace GlobalTheory

theorem isAlgebraic_residueField_transport {X : Scheme.{0}} {w x : X} (h : w = x) {C : CommRingCat.{0}}
    (ψ : X.residueField w ⟶ C) (φ : X.residueField x ⟶ C)
    (e : Spec.map ψ ≫ X.fromSpecResidueField w = Spec.map φ ≫ X.fromSpecResidueField x)
    (hφ : letI := φ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField x) C) :
    letI := ψ.hom.toAlgebra; Algebra.IsAlgebraic (X.residueField w) C := by
  subst h
  have : ψ = φ := Spec.map_injective ((cancel_mono _).mp e)
  subst this
  exact hφ

theorem exists_mem_fiber_isAlgebraic_residueField :
    ∀ (Y X : Scheme.{0}) (π : Y ⟶ X) [LocallyOfFiniteType π] (y₀ : Y), ∃ y : Y, π y = π y₀ ∧
      (letI := (π.residueFieldMap y).hom.toAlgebra;
        Algebra.IsAlgebraic (X.residueField (π y)) (Y.residueField y)) := by
  intro Y X π _ y₀
  let x := π y₀
  let s : π.fiber x ⟶ Spec (X.residueField x) := π.fiberToSpecResidueField x
  haveI : LocallyOfFiniteType s := by
    show LocallyOfFiniteType (pullback.snd _ _)
    infer_instance
  haveI : JacobsonSpace (π.fiber x) := LocallyOfFiniteType.jacobsonSpace s
  have hx : y₀ ∈ Set.range (π.fiberι x) := by
    rw [π.range_fiberι]; rfl
  obtain ⟨y₀', -⟩ := hx
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set (π.fiber x)))
    ⟨y₀', trivial⟩ isClosed_univ.isLocallyClosed
  have h1 : LocallyOfFiniteType ((π.fiber x).fromSpecResidueField z) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((π.fiber x).fromSpecResidueField z ≫ s)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have halg : letI := φ.hom.toAlgebra;
      Algebra.IsAlgebraic (X.residueField x) ((π.fiber x).residueField z) := by
    letI : Algebra (X.residueField x) ((π.fiber x).residueField z) := φ.hom.toAlgebra
    haveI : Algebra.FiniteType (X.residueField x) ((π.fiber x).residueField z) := hft
    haveI : Module.Finite (X.residueField x) ((π.fiber x).residueField z) :=
      finite_of_finite_type_of_isJacobsonRing _ _
    exact Algebra.IsAlgebraic.of_finite _ _
  let y : Y := π.fiberι x z
  have hy : π y = x := by
    have : y ∈ Set.range (π.fiberι x) := ⟨z, rfl⟩
    rw [π.range_fiberι] at this
    exact this
  refine ⟨y, hy, ?_⟩
  let g := (π.fiberι x).residueFieldMap z
  let ψ := π.residueFieldMap y ≫ g
  have e : Spec.map ψ ≫ X.fromSpecResidueField (π y) = Spec.map φ ≫ X.fromSpecResidueField x := by
    have e2 : π.fiberι x ≫ π = s ≫ X.fromSpecResidueField x := pullback.condition
    rw [hφ, Category.assoc, ← e2, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  have hψ := isAlgebraic_residueField_transport hy ψ φ e halg
  letI : Algebra (X.residueField (π y)) (Y.residueField y) := (π.residueFieldMap y).hom.toAlgebra
  letI : Algebra (Y.residueField y) ((π.fiber x).residueField z) := g.hom.toAlgebra
  letI : Algebra (X.residueField (π y)) ((π.fiber x).residueField z) := ψ.hom.toAlgebra
  haveI : IsScalarTower (X.residueField (π y)) (Y.residueField y) ((π.fiber x).residueField z) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsAlgebraic.tower_bot_of_injective (R := X.residueField (π y)) (A := (π.fiber x).residueField z) g.hom.injective

end GlobalTheory
