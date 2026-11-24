module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem bounded_operators_square_integrable : BoundedOperatorsSquareIntegrable := by
  intro P L hTT hL b hb u hu π
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le
  have hPW : ∃ C, Formalism.FourierDecayAlt.P.MAx3.I4.PW b C := by
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact Formalism.FourierDecayAlt.P.MAx3.I4.PW_gen hTT hL hLaw hx
    | one => exact ⟨1, Formalism.FourierDecayAlt.P.MAx3.I4.PW_one⟩
    | mul x y _ _ h1 h2 =>
      obtain ⟨C1, h1⟩ := h1
      obtain ⟨C2, h2⟩ := h2
      exact ⟨_, Formalism.FourierDecayAlt.P.MAx3.I4.PW_mul h1 h2⟩
  obtain ⟨C, hC0, Mx, hMb, hMe⟩ := hPW
  have hmeas := jd_evQ_meas P (MA.actA P b u π)
  have hL2u : ∀ π', MemLp (MA.evQ P (u π')) 2 (MA.mu0 P.r P.TT) := fun π' =>
    (memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π'))).2 (hu π')
  have hs : MemLp (fun q => ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) :=
    memLp_finsetSum _ fun π' _ => (hL2u π').norm
  have hg : MemLp (fun q => C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) := hs.const_mul C
  refine (memLp_two_iff_integrable_sq_norm hmeas).1 (hg.of_le hmeas (Filter.Eventually.of_forall fun q => ?_))
  rw [hMe u q π]
  calc ‖∑ π', Mx q π π' * MA.evQ P (u π') q‖ ≤ ∑ π', ‖Mx q π π' * MA.evQ P (u π') q‖ := norm_sum_le _ _
    _ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := Finset.sum_le_sum fun π' _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)
    _ = C * ∑ π', ‖MA.evQ P (u π') q‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖‖ := le_abs_self _

end

end Formalism.FourierDecayAlt.P.CutMP
