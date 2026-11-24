module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
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

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

theorem _root_.GlobalTheory.T.gramChart_sub_form_entry_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  first | exact @GlobalTheory.GramChartNear.gw_sub_jd_le | exact GlobalTheory.GramChartNear.gw_sub_jd_le | (intros; apply GlobalTheory.GramChartNear.gw_sub_jd_le <;> assumption)
