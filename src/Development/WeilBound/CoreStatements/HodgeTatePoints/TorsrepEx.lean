module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.FormalChartAtZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

noncomputable section

namespace PositivityTheory.HtPt.Rg

theorem torsrep_ex : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) := by
  intro R _ _ p hp A _ L hA hL ha
  have := hA.comm
  obtain ⟨hf, hfl, -⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow R A L
    (L.pull (fst A A).left) hA hL ha (LB.isLB_pull hL _)).2 p hp
  obtain ⟨B, cr, al, al', tw, hfree, hfin, y, hy, hu⟩ :=
    GlobalTheory.finRep_kernel_mul_finite_free A (LAlg.mk R : LAlg R) p hf hfl hA.smooth
  have e : al = al' := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    have := @IsScalarTower.algebraMap_apply R R B _ _ _ _ al al' tw r
    exact this.symm
  subst e
  refine ⟨{ A := B, cr := cr, alg := al, free := hfree, fin := hfin, y := y, y_p := hy, univ := ?_ }⟩
  intro S _ _ z hz
  exact hu S z hz

end PositivityTheory.HtPt.Rg
