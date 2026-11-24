module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_isometric_chart_blockHermitian : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q, Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧ (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧ ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) → ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  first | exact @GlobalTheory.CartanInt.HermChart.exists_chart | exact GlobalTheory.CartanInt.HermChart.exists_chart | (intros; apply GlobalTheory.CartanInt.HermChart.exists_chart <;> assumption)
