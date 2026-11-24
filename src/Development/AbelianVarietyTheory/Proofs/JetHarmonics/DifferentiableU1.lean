module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRingEquivApplyEqMulOfTranscendental
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.JetAlg

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_sub_one_lt {y : ℂ_[p]} {k : ℕ} (h : y ^ p ^ k = 1) : ‖y - 1‖ < 1 := by
  apply GlobalTheory.MomOne.ShiftComp.norm_sub_one_lt_of_root <;> assumption

theorem bd_derivative {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (PowerSeries.derivative f) := by
  intro n
  rw [coeff_derivative, norm_mul]
  refine mul_le_one₀ (hf _) (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  simpa using this

theorem bd_DT {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (DT f) := by
  have h := bd_derivative hf
  intro n
  rw [DT, add_mul, one_mul, map_add (f := _)]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h n) ?_)
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul]; exact h n

theorem bd_iterate {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (DT^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact bd_DT ih

theorem differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem differentiable_W1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (W1 d x F) := by
  have := differentiable_U1 d x hF
  unfold W1
  fun_prop

end GlobalTheory.MomOne.JetAlg

namespace GlobalTheory.MomOne
open JetAlg

theorem jets_algebraic : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ) → ∀ (ι : ℂ ≃+* ℂ_[q]) (t y : ℂ) (n s k : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y → δ⁻¹ ^ k * iteratedDeriv k (W1 d y (U1 d t θ)) 0 ∈ algebraicClosure ℚ ℂ := by
  intro d q hq δ θ hd hd16 hsp hθ hδ hL ι t y n s k hs ht hy
  refine mem_algebraicClosure_of_norm_le q ι _ 1 ?_
  intro ι' hι'
  obtain ⟨Ω, hΩ, h1', h2', -⟩ := hL ι'
  obtain ⟨hA, hB, -⟩ := okArith d q ι hd hd16 hsp
  have hy' : Good ι' d n s y := by
    obtain ⟨v, hv, hn, rfl⟩ := hy
    refine ⟨v, hv, ?_, rfl⟩
    have hc : InOK d (conj v) := (hA.2.2 v v hv hv).2.2.2
    have := hι' ⟨conj v, (hB _ hc).2.2⟩
    simp only at this
    rw [this]; exact hn
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (by simpa using hs) hq.out.ne_one
    · exact h
  obtain ⟨hζ, hE⟩ := h2' t y n s hs ht hy'
  have hb := (Shift.shift_laws q _ (norm_sub_one_lt hζ)).1 _ _ (h1' t ⟨s, hs0, hs, ht⟩)
  rw [← hE] at hb
  have han : AnalyticAt ℂ (W1 d y (U1 d t θ)) 0 :=
    (differentiable_W1 d y (differentiable_U1 d t hθ.1)).analyticAt 0
  have hk := (hat_multiplicative_chart q ι' (Ω / ι' δ) _ han).2.1 k
  have hc := bd_iterate hb k 0
  rw [coeff_zero_eq_constantCoeff_apply, hk, div_eq_mul_inv, mul_pow, mul_assoc, norm_mul, norm_pow, hΩ,
    one_pow, one_mul] at hc
  rw [map_mul, map_pow, map_inv₀]
  exact hc

end GlobalTheory.MomOne
