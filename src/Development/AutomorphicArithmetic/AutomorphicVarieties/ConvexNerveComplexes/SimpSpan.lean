module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Perturb
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.simp_span :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, LocFin q → ∀ (n : ℕ) (t : Fin (n + 1) → Vert q), t ∈ simp q T (n + 1) → ∀ k ∈ T, (∀ y, (∀ j, q y (t j).1 = 1) → q y k = 0) → k = 0 := by
  intro E Y _ _ q T hq n t ht k hk hkq
  obtain ⟨x, hx, hxt⟩ := ht
  by_contra hk0
  have hxk : 0 < x k := hx k hk hk0
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) + 1 := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  obtain ⟨c, hc⟩ : ∃ c : E, c = N⁻¹ • ∑ j, (t j).1 := ⟨_, rfl⟩
  have hlin : ∀ f : E →L[ℝ] ℝ, f c = N⁻¹ * ∑ j, f (t j).1 := by
    intro f

    rw [hc, map_smul, map_sum, smul_eq_mul]
  have hpoly : ∀ j, (t j).1 ∈ poly q := fun j => (t j).2.1
  have hconst : ∀ a : ℝ, (∑ _j : Fin (n + 1), a) = N * a := by
    intro a
    simp [hN]
  have hcpoly : c ∈ poly q := by
    intro y
    rw [hlin, le_inv_mul_iff₀ hNpos]
    have h1 := hconst 1
    rw [mul_one] at h1
    rw [mul_one, ← h1]
    exact Finset.sum_le_sum fun j _ => hpoly j y
  have htight : ∀ y, q y c = 1 → ∀ j, q y (t j).1 = 1 := by
    intro y hy j
    rw [hlin, inv_mul_eq_one₀ hNpos.ne'] at hy
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ q y (t i).1 - 1 := fun i _ => sub_nonneg.mpr (hpoly i y)
    have hz : ∑ i, (q y (t i).1 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, ← hy, hconst, mul_one, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j (Finset.mem_univ j)
    linarith
  obtain ⟨ε, hε, hpert⟩ := perturb hq c hcpoly k (fun y hy => hkq y (htight y hy))
  have hmem : c + (-ε) • k ∈ poly q := hpert (-ε) (by rw [abs_neg, abs_of_pos hε])
  have hsum_le : ∑ j, x (t j).1 ≤ N * x (c + (-ε) • k) := by
    rw [← hconst]
    exact Finset.sum_le_sum fun j _ => hxt j _ hmem
  have hexp : x (c + (-ε) • k) = x c - ε * x k := by
    rw [map_add (f := _), map_smul, smul_eq_mul]
    ring
  have hxc : N * x c = ∑ j, x (t j).1 := by
    rw [hlin x, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  rw [hexp, ← hxc] at hsum_le
  nlinarith [mul_pos hNpos (mul_pos hε hxk)]
