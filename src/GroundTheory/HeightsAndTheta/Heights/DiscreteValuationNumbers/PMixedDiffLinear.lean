module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section MixedDiffLinearProof

variable {K : Type*}

theorem diffStep_add' (b : K → ℤ) (f g : (K → ℤ) → ℤ) :
    diffStep b (f + g) = diffStep b f + diffStep b g := by
  funext m; simp only [diffStep, Pi.add_apply]; ring

theorem diffStep_smul' (b : K → ℤ) (c : ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (c • f) = c • diffStep b f := by
  funext m; simp only [diffStep, Pi.smul_apply, smul_eq_mul]; ring

theorem diffStep_shiftFn' (b s : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (shiftFn s f) = shiftFn s (diffStep b f) := by
  funext m; simp only [diffStep, shiftFn, sub_right_comm]

theorem diffStep_comm' (b b' : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' f) = diffStep b' (diffStep b f) := by
  funext m; simp only [diffStep, sub_right_comm m b b']; ring

theorem foldr_diffStep_props (l : List (K → ℤ)) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ) :
    l.foldr diffStep (f + g) = l.foldr diffStep f + l.foldr diffStep g ∧
    l.foldr diffStep (c • f) = c • l.foldr diffStep f ∧
    l.foldr diffStep (shiftFn s f) = shiftFn s (l.foldr diffStep f) ∧
    l.foldr diffStep (diffStep b f) = diffStep b (l.foldr diffStep f) := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, diffStep_add']
    · rw [h2, diffStep_smul']
    · rw [h3, diffStep_shiftFn']
    · rw [h4, diffStep_comm']

theorem MixedDiffLinear.proof : MixedDiffLinear.Statement := by
  intro K n bs f g c s b
  obtain ⟨h1, h2, h3, h4⟩ := foldr_diffStep_props (List.ofFn bs) f g c s b
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold mixedDiff
  rw [List.ofFn_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, List.foldr_cons]

end MixedDiffLinearProof

end GroundTheory.Heights₂.Heights.NumbersDVR
