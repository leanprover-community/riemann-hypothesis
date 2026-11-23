module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
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

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

open Matrix

theorem inv_mul_coeff_eq_of_X_pow_mul {K : Type} [Field K] {N : ℕ} {c : K} (hc : c ≠ 0)
    {f g : K⟦X⟧} (h : X ^ N * f = c • g) (k : ℕ) : c⁻¹ * coeff k f = coeff (k + N) g := by
  have := congrArg (coeff (k + N)) h
  rw [coeff_X_pow_mul, coeff_smul, smul_eq_mul] at this
  rw [this, inv_mul_cancel_left₀ hc]

theorem mem_lpow_L_of_vpow_smul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι) (hw : w ∈ P.L)
    (hz : z ∈ P.L) (h : ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z) :
    ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  have hc : (l : K) ^ b ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ b)⁻¹ • w, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_,
    (smul_inv_smul₀ hc w).symm⟩
  have hm := P.mem_extc_iff.1 (mem_tot.1 hw τ)
  have hm' := P.mem_extc_iff.1 (mem_tot.1 hz τ)
  have hi : X ^ (e * n) * (P.mxInv τ *ᵥ w τ) i = (l : K) ^ b • (P.mxInv τ *ᵥ z τ) i := by
    have hτ := congrArg (fun v : Vec K a ι => (P.mxInv τ *ᵥ v τ) i) h
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul] at hτ
    rw [pow_mul]
    exact hτ
  rw [mem_A]
  intro k
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, coeff_smul, smul_eq_mul,
    inv_mul_coeff_eq_of_X_pow_mul hc hi]
  exact mem_A.1 (hm' i) _

end GlobalTheory.CokerL
