module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.AutomorphicForms.AdelicGLn
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem one_le_ht {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (y : GL (Fin a) (TR.Rinf E)) : 1 ≤ TR.height y := by
  unfold TR.height
  have := norm_nonneg (TR.toL y.val)
  have := norm_nonneg (TR.toL (y⁻¹).val)
  linarith

private theorem unif {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ} (φ : TR.Sm E a)
    (hl : IsOpen {k | TR.finRep E a k φ = φ})
    (hg : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * TR.infGL E a y)‖ ≤ C * TR.height y ^ N)
    {Ω : Set (AdelicGLn.FiniteAdelicGL E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k ∈ Ω, ∀ y, ‖φ.1 (finGL E a k * TR.infGL E a y)‖ ≤ C * TR.height y ^ N := by
  refine hΩ.induction_on (p := fun S => ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ k ∈ S, ∀ y,
    ‖φ.1 (finGL E a k * TR.infGL E a y)‖ ≤ C * TR.height y ^ N) ⟨0, 0, le_rfl, fun _ h => h.elim⟩ ?_ ?_ ?_
  · rintro s t hst ⟨C, N, hC, h⟩
    exact ⟨C, N, hC, fun k hk => h k (hst hk)⟩
  · rintro s t ⟨C, N, hC, h⟩ ⟨C', N', hC', h'⟩
    refine ⟨max C C', max N N', hC.trans (le_max_left _ _), fun k hk y => ?_⟩
    have h1 := one_le_ht y
    rcases hk with hk | hk
    · exact (h k hk y).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1 (le_max_left _ _))
        (pow_nonneg (zero_le_one.trans h1) _) (hC.trans (le_max_left _ _)))
    · exact (h' k hk y).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1 (le_max_right _ _))
        (pow_nonneg (zero_le_one.trans h1) _) (hC.trans (le_max_left _ _)))
  · intro x _
    obtain ⟨C, N, h⟩ := hg (finGL E a x)
    have ho : IsOpen ((fun k : AdelicGLn.FiniteAdelicGL E a => x⁻¹ * k) ⁻¹' {k | TR.finRep E a k φ = φ}) :=
      hl.preimage (continuous_const.mul continuous_id)
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds ?_), |C|, N, abs_nonneg C, fun k hk y => ?_⟩
    · change TR.finRep E a (x⁻¹ * x) φ = φ
      rw [inv_mul_cancel, map_one]
      rfl
    · have e : φ.1 (finGL E a x * TR.infGL E a y * finGL E a (x⁻¹ * k)) = φ.1 (finGL E a x * TR.infGL E a y) :=
        congrFun (congrArg Subtype.val hk) _
      rw [mul_assoc, TR.infGL_comm, ← mul_assoc, ← map_mul, mul_inv_cancel_left] at e
      rw [e]
      exact (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (zero_le_one.trans (one_le_ht y)) _))
