module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatio
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 → ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ < ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  first | exact @GlobalTheory.TiltRootApprox.exists_root_approx | exact GlobalTheory.TiltRootApprox.exists_root_approx | (intros; apply GlobalTheory.TiltRootApprox.exists_root_approx <;> assumption)
