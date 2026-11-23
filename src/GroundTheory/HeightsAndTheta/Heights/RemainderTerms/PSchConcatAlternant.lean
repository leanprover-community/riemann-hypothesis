module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchConcatAlternant.alternant_comp_perm {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]

theorem SchConcatAlternant.alternant_add_staircase {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by
  rw [mul_comm, ← Schur.det_pow_add_staircase_eq, ← Matrix.det_transpose]
  rfl

theorem SchConcatAlternant.proof (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]

end

end GroundTheory.Heights₂.Heights.RestTerms
