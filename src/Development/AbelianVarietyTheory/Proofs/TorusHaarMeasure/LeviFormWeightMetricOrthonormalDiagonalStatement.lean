module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
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

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.leviForm_weightMetric_orthonormal_diagonal : (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → ∀ ξ : Fin (nd X) → ℂ, leviM X (phla X la) x 0 ξ = ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 * ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2) := by
  first | exact @GlobalTheory.LeviZero.leviZero | exact GlobalTheory.LeviZero.leviZero | (intros; apply GlobalTheory.LeviZero.leviZero <;> assumption)
