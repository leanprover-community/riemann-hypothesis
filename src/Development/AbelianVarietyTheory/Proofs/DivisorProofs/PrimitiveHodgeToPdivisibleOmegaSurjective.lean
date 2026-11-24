module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallApplyHodgePrimitiveEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianSchemeStatement
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem surjective_of_isCan_field :
    GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K], (p : K) = 0 →
    ∀ (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (G : PDivGroup p K) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[K] G.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
      Function.Surjective ψ := by
  intro hH p _ K _ hp A _ g hA hg G t ψ hψ
  have hL : LieExact A :=
    GlobalTheory.T.hodgeLieSequence_exact_abelianScheme
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH K A g hA hg
  have hx := GlobalTheory.T.eq_zero_of_forall_apply_hodgePrimitive_eq_zero p K 1 (by rw [pow_one]; exact hp) A hA hL G t ψ hψ
  rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
  intro x hx0
  exact hx x fun c ↦ by simpa using LinearMap.congr_fun hx0 c

end GlobalTheory.PtExt
