module

public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLG

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V']

def Bdd (F : ℤ → V') (m₀ : ℤ) : Prop := ∀ i < m₀, F i = 0

theorem serMul_eq_sum (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) (M : ℕ)
    (hM : (i - m₀).toNat + 1 ≤ M) :
    serMul P F i = ∑ k ∈ Finset.range M, PowerSeries.coeff k P • F (i - k) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hkM
  apply hk
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_bdd (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) : Bdd (serMul P F) m₀ := by
  intro i hi
  unfold serMul
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_serMul (P Q : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) :
    serMul P (serMul Q F) i = serMul (P * Q) F i := by
  set N := (i - m₀).toNat + 1 with hN
  rw [serMul_eq_sum P (serMul_bdd Q hF) i N le_rfl, serMul_eq_sum (P * Q) hF i N le_rfl]
  have hL : ∀ k ∈ Finset.range N, PowerSeries.coeff k P • serMul Q F (i - k) =
      ∑ j ∈ Finset.range (N - k), (PowerSeries.coeff k P * PowerSeries.coeff j Q) • F (i - (k + j : ℕ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [serMul_eq_sum Q hF (i - k) (N - k) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hL]
  have hR : ∀ s ∈ Finset.range N, PowerSeries.coeff s (P * Q) • F (i - s) =
      ∑ k ∈ Finset.Ico 0 (s + 1), (PowerSeries.coeff k P * PowerSeries.coeff (s - k) Q) • F (i - s) := by
    intro s _
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul,
      Finset.range_eq_Ico]
  rw [Finset.sum_congr rfl hR, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.add_sub_cancel_left]

theorem serMul_X_pow (h : ℕ) (F : ℤ → V') (i : ℤ) :
    serMul (PowerSeries.X ^ h : PowerSeries LL) F i = F (i - h) := by
  unfold serMul
  rw [finsum_eq_single _ h (fun k hk => by rw [PowerSeries.coeff_X_pow, if_neg hk, zero_smul])]
  rw [PowerSeries.coeff_X_pow, if_pos rfl, one_smul]

theorem serMul_rescale (u : LL) (hu : u ≠ 0) (P : PowerSeries LL) (F : ℤ → V') (i : ℤ) :
    u ^ i • serMul P F i = serMul (PowerSeries.rescale u P) (fun j => u ^ j • F j) i := by
  unfold serMul
  rw [smul_finsum]
  refine finsum_congr (fun k => ?_)
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show u ^ i = u ^ (k : ℤ) * u ^ (i - k) by rw [← zpow_add₀ hu]; ring_nf, zpow_natCast]
  ring

end Formalism.MainNotions.N.Ln34.MLG

end
