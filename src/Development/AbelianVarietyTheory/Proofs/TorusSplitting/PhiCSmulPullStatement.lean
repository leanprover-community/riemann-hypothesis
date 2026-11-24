module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PhiCSmulPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symB_phiC_eq_mul_of_pullback : ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (X X' : Type) [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup X'] [Module (𝓞 E) X'] (e : X ≃ₗ[𝓞 E] X') (β' : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X') (t : ℝ), 0 ≤ t → ∃ β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj X, (∀ a b, (β : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) a b = t * (β' : X' →ₗ[ℤ] X' →ₗ[ℤ] ℝ) (e a) (e b)) ∧ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β = t * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β' := by
  first | exact @GlobalTheory.EtaVal.phiC_smul_pull | exact GlobalTheory.EtaVal.phiC_smul_pull | (intros; apply GlobalTheory.EtaVal.phiC_smul_pull <;> assumption)
