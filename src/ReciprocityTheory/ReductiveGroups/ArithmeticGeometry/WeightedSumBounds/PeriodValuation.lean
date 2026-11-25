module

public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

open ReciprocityTheory.PGsh PowerSeries

noncomputable section

section Val

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

theorem exists_real {x : K} (hx : x ≠ 0) : ∃ r : ℝ, v x = r := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((v.top_iff).not.mpr hx)
  exact ⟨r, hr.symm⟩

theorem nsmul_one_coe (n : ℕ) : n • (1 : WithTop ℝ) = ((n : ℝ) : WithTop ℝ) := by
  rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]

theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact v.map_le_add ih (le_of_eq v.map_one.symm)

theorem intCast_nonneg (n : ℤ) : 0 ≤ v (n : K) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using natCast_nonneg v m
  · simpa [v.map_neg] using natCast_nonneg v m

theorem natCast_eq_zero_of_coprime {p : ℕ} (hp1 : v (p : K) = 1) {c : ℕ}
    (hc : Nat.Coprime p c) : v (c : K) = 0 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have hK : (a : K) * p + b * c = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have h0 := natCast_nonneg v c
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have h1 : 0 < v ((a : K) * p) := by
    rw [v.map_mul, hp1]
    calc (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
      _ = 0 + 1 := (zero_add 1).symm
      _ ≤ v (a : K) + 1 := add_le_add_left (intCast_nonneg v a) 1
  have h2 : 0 < v ((b : K) * c) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_left (intCast_nonneg v b))
  have h3 := v.map_add ((a : K) * p) ((b : K) * c)
  rw [hK, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

theorem natCast_eq_factorization {p : ℕ} (hp : p.Prime) (hp1 : v (p : K) = 1) {m : ℕ}
    (hm : m ≠ 0) : v (m : K) = ((m.factorization p : ℝ) : WithTop ℝ) := by
  have e := Nat.ordProj_mul_ordCompl_eq_self m p
  have hc := Nat.coprime_ordCompl hp hm
  conv_lhs => rw [← e]
  rw [Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hp1,
    natCast_eq_zero_of_coprime v hp1 hc, add_zero, nsmul_one_coe]

theorem div_eq_coe {x y : K} (hy : y ≠ 0) {A B : ℝ} (hx : v x = A) (hyv : v y = B) :
    v (x / y) = ((A - B : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := exists_real v (inv_ne_zero hy)
  have h1 : v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, v.map_one]
  rw [v.map_mul, hyv, hc, ← WithTop.coe_add] at h1
  have h2 : B + c = 0 := WithTop.coe_eq_zero.mp h1
  rw [div_eq_mul_inv, v.map_mul, hx, hc, ← WithTop.coe_add]
  congr 1
  linarith

end Val

section ZetaNonvanishing₂

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

end ZetaNonvanishing₂

end

end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
