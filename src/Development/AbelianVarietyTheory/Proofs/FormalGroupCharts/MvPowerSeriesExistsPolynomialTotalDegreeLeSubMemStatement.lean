module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | exact GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | (intros; apply GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem <;> assumption)
