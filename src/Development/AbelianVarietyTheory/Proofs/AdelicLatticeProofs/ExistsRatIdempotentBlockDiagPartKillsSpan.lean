module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspaceStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimpleStatement
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

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_blk_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨W, hWinv, hWσ, a, ha_span, ha0, ha_into, ha_kill⟩ := GlobalTheory.T.invariant_subspace_not_semisimple ι Γ hΓ hss
  obtain ⟨e, hee, hW⟩ := GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace ι W hWσ

  have hEE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, hee]
  have hEmem : ∀ v, e.map (algebraMap ℚ ℂ) *ᵥ v ∈ W := fun v => by
    rw [hW, Matrix.mulVec_mulVec, hEE]
  have hfix : ∀ w ∈ W, e.map (algebraMap ℚ ℂ) *ᵥ w = w := fun w hw => (hW w).1 hw
  refine ⟨e, hee, ?_, a, ha_span, ha0, ?_⟩
  ·
    intro g hg
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hfix _ (hWinv g hg _ (hEmem v)), sub_self, Matrix.zero_mulVec]
  ·
    rw [Matrix.ext_iff_mulVec]
    intro v
    unfold blk
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_kill _ (hEmem v),
      Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (ha_into _), sub_self, Matrix.zero_mulVec]

end GlobalTheory.ClassFin
