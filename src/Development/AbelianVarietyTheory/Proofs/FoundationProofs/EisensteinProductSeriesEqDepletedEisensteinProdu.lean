module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem zm_eq_mul_dep_eis : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  intro k l j u w A A' c c' hjk
  funext n
  unfold Zm mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1) p.1 * dep l (eis (j + 1) c' A' w) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    have hsw : ∑ q ∈ p.2.divisorsAntidiagonal, A' (q.1 : ℤ) * ((q.1 : ℂ)) ^ (j + 1 - 1) * w (q.2 : ℤ)
        = ∑ y ∈ p.2.divisorsAntidiagonal, A' (y.2 : ℤ) * ((y.2 : ℂ)) ^ (j + 1 - 1) * w (y.1 : ℤ) := by
      refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun q => ?_) (fun q _ => rfl)
      simp only [Nat.mem_divisorsAntidiagonal, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
    rw [hsw, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
