module

public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem cf_last_isEmpty (r : ℕ) : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun l => by have := l.1.isLt; have := l.2; simp at *; omega⟩

theorem integrable_cf_last {r : ℕ} (f : Cf r (Fin.last r) → ℂ) : Integrable f := by
  haveI := cf_last_isEmpty r
  have hvol : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (fun l => isEmptyElim l) := by
    rw [volume_pi, Measure.pi_of_empty]
  haveI : IsFiniteMeasure (volume : Measure (Cf r (Fin.last r))) := by rw [hvol]; infer_instance
  have hf : f = fun _ => f (fun l => isEmptyElim l) := by
    funext c'
    congr 1
    funext l
    exact isEmptyElim l
  rw [hf]
  exact integrable_const _

end Formalism.FourierDecayAlt.P5.HerC
