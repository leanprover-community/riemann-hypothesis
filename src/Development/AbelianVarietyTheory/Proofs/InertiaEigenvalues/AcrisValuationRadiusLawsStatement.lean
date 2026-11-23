module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLaws
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisValuation_radius_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 → (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧ (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧ (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧ ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  first | exact @GlobalTheory.PMon.Gauss.vr_laws | exact GlobalTheory.PMon.Gauss.vr_laws | (intros; apply GlobalTheory.PMon.Gauss.vr_laws <;> assumption)
