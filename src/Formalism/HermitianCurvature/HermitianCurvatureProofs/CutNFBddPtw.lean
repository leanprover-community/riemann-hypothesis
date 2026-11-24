module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem pointwise_bound_normal_form_holds : NFBddPtw := by
  intro P L hTT hL b hb
  obtain ⟨C, Mx, hSA, hC, hM⟩ := Formalism.FourierDecayAlt.P.MAx3.AD.SAB_closure (hTTp := hTT) (hL := hL)
    (hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le) hb
  refine ⟨(Fintype.card (M.Ty P) : ℝ) * ((Fintype.card (M.Ty P) : ℝ) * C ^ 2), fun u q => ?_⟩
  have key : ∀ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤
      (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) := by
    intro ρ
    rw [hSA.1 u q ρ]
    have h1 : ‖∑ π', Mx q ρ π' * MA.evQ P (u π') q‖ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM q ρ π') (norm_nonneg _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (M.Ty P)))
      (f := fun π' => C * ‖MA.evQ P (u π') q‖)
    calc _ ≤ (∑ π', C * ‖MA.evQ P (u π') q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by
        rw [Finset.card_univ]
        simp only [mul_pow, ← Finset.mul_sum]
  calc _ ≤ ∑ ρ : M.Ty P, (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) :=
        Finset.sum_le_sum fun ρ _ => key ρ
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end

end Formalism.FourierDecayAlt.P.CutBP
