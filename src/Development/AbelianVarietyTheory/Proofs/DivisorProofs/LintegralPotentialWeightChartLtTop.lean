module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds

@[expose] public section

namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

theorem lintegral_kaF_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  intro E _ _ _ r X x0 ho
  obtain ⟨FF, hF⟩ := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  have hfin := (GlobalTheory.TrueCx.covol_eq X ho hF).1
  refine ⟨4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1, fun s hs => ?_⟩
  obtain ⟨C, hC, hCb⟩ := kaUnfoldStatement_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) FF hF s
    (by linarith)
  have h := hCb (fun _ => 1) measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul] at h
  exact h.trans_lt (ENNReal.mul_lt_top hC hfin)

end GlobalTheory.ScalarPoin
