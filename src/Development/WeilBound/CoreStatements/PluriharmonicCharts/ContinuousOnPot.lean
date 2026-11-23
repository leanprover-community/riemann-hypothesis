module

public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsMultiHomogMapConj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Filter Topology

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem contDiff_nd (a : K → ℕ) : ContDiff ℝ ∞ (nd (J := J) a) := by
  unfold nd
  refine contDiff_prod fun k _ => ?_
  refine (ContDiff.sum fun i _ => ?_).pow _
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) _)

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem smoothOn_pot {V : Set X} {ι' : Type} [Fintype ι'] (f : ι' → X → ℂ) (hf : ∀ j, A.HoloOn V (f j))
    (g : X → (Σ k, J k) → ℂ) (hg : ∀ p, A.HoloOn V (fun y => g y p)) (a : ι' → K → ℕ)
    (hnd : ∀ y ∈ V, ∀ j, 0 < nd (a j) (g y)) (hpos : ∀ y ∈ V, 0 < ∑ j, ‖f j y‖ ^ 2 / nd (a j) (g y)) (c : ℝ) :
    A.SmoothOn V (fun y => c - (1 / 2) * Real.log (∑ j, ‖f j y‖ ^ 2 / nd (a j) (g y))) := by
  intro ch t ht
  apply ContDiffAt.contDiffWithinAt
  have h1 : ∀ j, ContDiffAt ℝ ∞ (fun s => ‖f j ((A.chart ch).symm s)‖ ^ 2) t := fun j =>
    (contDiff_norm_sq ℝ).contDiffAt.comp t (((hf j ch t ht).contDiffAt).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ ∞ (fun s => g ((A.chart ch).symm s)) t :=
    contDiffAt_pi.2 fun p => ((hg p ch t ht).contDiffAt).restrict_scalars ℝ
  have h3 : ∀ j, ContDiffAt ℝ ∞ (fun s => nd (a j) (g ((A.chart ch).symm s))) t := fun j =>
    (contDiff_nd (a j)).contDiffAt.comp t h2
  have hsum : ContDiffAt ℝ ∞ (fun s => ∑ j, ‖f j ((A.chart ch).symm s)‖ ^ 2 / nd (a j) (g ((A.chart ch).symm s))) t :=
    ContDiffAt.sum fun j _ => (h1 j).div (h3 j) (ne_of_gt (hnd _ ht.2 j))
  exact contDiffAt_const.sub (contDiffAt_const.mul (hsum.log (ne_of_gt (hpos _ ht.2))))

end PositivityTheory.Xgp.c_bm_exists_boundary
