module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormLineSectionPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

namespace ReciprocityTheory.ChartRestriction.G.T0

theorem hups_choose_ratio (n p : ℕ) (hp : p ≤ n) : ∀ a : ℕ,
    (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a := by
  intro a
  induction a with
  | zero => simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, le_refl]
  | succ a ih =>
    have hA := Nat.add_one_mul_choose_eq (n + a) a
    have hB := Nat.add_one_mul_choose_eq (p + a) a
    rw [← Nat.add_assoc n a 1, ← Nat.add_assoc p a 1]
    have hA' : (((n + a + 1).choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) =
        ((n : ℝ) + a + 1) * (((n + a).choose a : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        congrArg (fun t : ℕ => (t : ℝ)) hA.symm
    have hB' : (((p + a + 1).choose (a + 1) : ℕ) : ℝ) * ((a : ℝ) + 1) =
        ((p : ℝ) + a + 1) * (((p + a).choose a : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        congrArg (fun t : ℕ => (t : ℝ)) hB.symm
    have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hpn : (p : ℝ) ≤ n := Nat.cast_le.mpr hp
    have hkey : ((n : ℝ) + a + 1) * ((p : ℝ) + 1) ≤ ((p : ℝ) + a + 1) * ((n : ℝ) + 1) := by
      linarith only [mul_nonneg (Nat.cast_nonneg a) (sub_nonneg.mpr hpn)]
    have hX : 0 ≤ (((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a := by positivity
    rw [← mul_le_mul_iff_of_pos_right ha1]
    calc (((n + a + 1).choose (a + 1) : ℕ) : ℝ) * ((p : ℝ) + 1) ^ (a + 1) * ((a : ℝ) + 1)
        = (((n : ℝ) + a + 1) * ((p : ℝ) + 1)) *
            ((((n + a).choose a : ℕ) : ℝ) * ((p : ℝ) + 1) ^ a) := by
          rw [pow_succ]; linear_combination ((p : ℝ) + 1) ^ a * ((p : ℝ) + 1) * hA'
      _ ≤ (((p : ℝ) + a + 1) * ((n : ℝ) + 1)) *
            ((((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a) :=
          mul_le_mul hkey ih hX (by positivity)
      _ = (((p + a + 1).choose (a + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (a + 1) * ((a : ℝ) + 1) := by
          rw [pow_succ]; linear_combination -(((n : ℝ) + 1) ^ a * ((n : ℝ) + 1)) * hB'

theorem hups_pow_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ Real.exp (k * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (add_nonneg zero_le_one hx) (by rw [add_comm]; exact Real.add_one_le_exp x) k

theorem hups_choose_exp (n p a : ℕ) (hp : p ≤ n) :
    (((n + a).choose a : ℕ) : ℝ) ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by
  have h1 := hups_choose_ratio n p hp a
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hcast : (((n - p : ℕ) : ℝ)) = (n : ℝ) - p := by rw [Nat.cast_sub hp]
  have hx : 0 ≤ (((n - p : ℕ) : ℝ)) / ((p : ℝ) + 1) := by positivity
  have h2 := hups_pow_exp _ hx a
  have e : 1 + (((n - p : ℕ) : ℝ)) / ((p : ℝ) + 1) = ((n : ℝ) + 1) / ((p : ℝ) + 1) := by
    rw [hcast, one_add_div hp1.ne', add_right_comm,
      add_comm (p : ℝ) ((n : ℝ) - p), sub_add_cancel]
  rw [e, div_pow] at h2
  have hpa : (0 : ℝ) < ((p : ℝ) + 1) ^ a := by positivity
  have hB : (0 : ℝ) ≤ (((p + a).choose a : ℕ) : ℝ) := by positivity
  have h3 : (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a / ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 hB
  refine le_trans ?_ h3
  rw [le_div_iff₀ hpa]
  exact h1



theorem hups_ratio (D N n n' deF u del : ℕ) (h1 : 1 ≤ deF) (hdel : deF ≤ del)
    (hu : u ≤ (D + 1) * del) (hn : 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del ≤ n)
    (hn' : n' = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del) :
    (n : ℝ) * cardUX D N n n' ≤ ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by
  have hdel1 : 1 ≤ del := le_trans h1 hdel
  have hM1 : D + 2 ≤ (D + 2) * (N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos N)
  have hbig : del ≤ n := by
    have : 1 ≤ 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) := Nat.succ_le_of_lt (by positivity)
    calc del = 1 * del := (one_mul _).symm
      _ ≤ 8 * ((D + 2) * (N + 1)) ^ 2 * (D + 1) * del := Nat.mul_le_mul_right _ this
      _ ≤ n := hn
  have haN : deF ≤ n := le_trans hdel hbig
  have hn1 : 1 ≤ n := le_trans hdel1 hbig
  have huN : u ≤ n' := by
    have : 1 ≤ 8 * n * ((D + 2) * (N + 1)) :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.lt_of_succ_le hn1)) (by positivity))
    rw [hn']
    calc u ≤ (D + 1) * del := hu
      _ = 1 * ((D + 1) * del) := (one_mul _).symm
      _ ≤ 8 * n * ((D + 2) * (N + 1)) * ((D + 1) * del) := Nat.mul_le_mul_right _ this
      _ = 8 * n * ((D + 2) * (N + 1)) * (D + 1) * del := (mul_assoc _ _ _).symm
  have hA := hups_choose_exp n (n - deF) (D + 1) (Nat.sub_le n deF)
  have hB := hups_choose_exp n' (n' - u) ((D + 2) * (N + 1)) (Nat.sub_le n' u)
  rw [Nat.sub_sub_self haN] at hA
  rw [Nat.sub_sub_self huN] at hB
  have hc1 : (cardUX D N n n' : ℝ) = (((n + (D + 1)).choose (D + 1) : ℕ) : ℝ) *
      (((n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) := by
    simp only [cardUX, Nat.cast_mul, Nat.add_assoc n D 1]
  have hc2 : (cardUX D N (n - deF) (n' - u) : ℝ) = (((n - deF + (D + 1)).choose (D + 1) : ℕ) : ℝ) *
      (((n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) := by
    simp only [cardUX, Nat.cast_mul, Nat.add_assoc (n - deF) D 1]
  set K : ℝ := ((D + 1 : ℕ) : ℝ) with hK
  set Mr : ℝ := (((D + 2) * (N + 1) : ℕ) : ℝ) with hMr
  set a : ℝ := (deF : ℝ) with ha
  set nr : ℝ := (n : ℝ) with hnr
  set dl : ℝ := (del : ℝ) with hdl
  set ur : ℝ := (u : ℝ) with hur
  set n'r : ℝ := (n' : ℝ) with hn'r
  have hK1 : 1 ≤ K := by rw [hK]; exact_mod_cast Nat.le_add_left 1 D
  have hMK : K + 1 ≤ Mr := by
    rw [hK, hMr]; exact_mod_cast hM1
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast h1
  have had : a ≤ dl := by rw [ha, hdl]; exact_mod_cast hdel
  have hud : ur ≤ K * dl := by rw [hur, hK, hdl]; exact_mod_cast hu
  have hnbig : 8 * Mr ^ 2 * K * dl ≤ nr := by
    rw [hnr, hMr, hK, hdl]; exact_mod_cast hn
  have hn'eq : n'r = 8 * nr * Mr * K * dl := by
    rw [hn'r, hnr, hMr, hK, hdl, hn']; push_cast; ring
  have hsub1 : (((n - deF : ℕ) : ℝ)) = nr - a := by rw [Nat.cast_sub haN]
  have hsub2 : (((n' - u : ℕ) : ℝ)) = n'r - ur := by rw [Nat.cast_sub huN]
  rw [hsub1] at hA
  rw [hsub2] at hB
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have ha0 : 0 ≤ a := zero_le_one.trans ha1
  have hKplus1 : 1 ≤ K + 1 := by linarith only [hK1]
  have hKplus0 : 0 ≤ K + 1 := zero_le_one.trans hKplus1
  have hMr1 : 1 ≤ Mr := hKplus1.trans hMK
  have h8 : (1 : ℝ) ≤ 8 := by norm_num
  have h80 : (0 : ℝ) ≤ 8 := zero_le_one.trans h8
  have hnr_ge : 8 * (K + 1) ^ 2 * K * a ≤ nr := by
    have hsq : (K + 1) ^ 2 ≤ Mr ^ 2 := pow_le_pow_left₀ hKplus0 hMK 2
    have hcoeff : 8 * (K + 1) ^ 2 * K ≤ 8 * Mr ^ 2 * K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq h80) hK0
    have hcoeff0 : 0 ≤ 8 * Mr ^ 2 * K := mul_nonneg (mul_nonneg h80 (sq_nonneg Mr)) hK0
    exact (mul_le_mul hcoeff had ha0 hcoeff0).trans hnbig
  have hKa0 : 0 ≤ (K + 1) * a := mul_nonneg hKplus0 ha0
  have hKa_le : (K + 1) * a ≤ nr := by
    have hfactor : 1 ≤ 8 * (K + 1) * K :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h8 hKplus1) hK1
    calc (K + 1) * a ≤ (8 * (K + 1) * K) * ((K + 1) * a) :=
          le_mul_of_one_le_left hKa0 hfactor
      _ = 8 * (K + 1) ^ 2 * K * a := by ring
      _ ≤ nr := hnr_ge
  have hnr1 : 1 ≤ nr := by simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hn1
  set y1 : ℝ := K * (a / (nr - a + 1)) with hy1
  set y2 : ℝ := Mr * (ur / (n'r - ur + 1)) with hy2
  set S : ℝ := nr + (K + 1) * a with hS
  have hSpos : 0 < S := add_pos_of_pos_of_nonneg (zero_lt_one.trans_le hnr1) hKa0
  have hd1 : 0 < nr - a + 1 :=
    add_pos_of_nonneg_of_pos (sub_nonneg.mpr ((Nat.cast_le (α := ℝ)).mpr haN)) zero_lt_one
  have hnrMr : 1 ≤ nr * Mr := one_le_mul_of_one_le_of_one_le hnr1 hMr1
  have hKdl0 : 0 ≤ K * dl := mul_nonneg hK0 (ha0.trans had)
  have hq : K * dl ≤ nr * Mr * K * dl := by
    simpa only [mul_assoc] using le_mul_of_one_le_left hKdl0 hnrMr
  have hd2 : 0 < n'r - ur + 1 :=
    add_pos_of_nonneg_of_pos (sub_nonneg.mpr ((Nat.cast_le (α := ℝ)).mpr huN)) zero_lt_one
  have hpoly : K * (K + 2) + 3 / 16 ≤ 3 / 2 * (K + 1) ^ 2 * K := by
    have ht := sub_nonneg.mpr hK1
    linarith only [hK1, sq_nonneg (K - 1), mul_nonneg (sq_nonneg (K - 1)) ht]
  have e1 : K * (K + 2) * a + 3 * a / 16 ≤ 3 * nr / 16 := by
    linarith only [mul_le_mul_of_nonneg_right hpoly ha0, hnr_ge]
  have hy1S : y1 * S ≤ K * a + 3 * a / 16 := by
    have : y1 * S = K * a * S / (nr - a + 1) := by
      rw [hy1, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [this, div_le_iff₀ hd1, hS]
    linarith only [mul_le_mul_of_nonneg_left e1 ha0, mul_nonneg hK0 ha0, ha0]
  have hy2S : y2 * S ≤ 1 / 2 := by
    have : y2 * S = Mr * ur * S / (n'r - ur + 1) := by
      rw [hy2, ← mul_div_assoc, div_mul_eq_mul_div]
    rw [this, div_le_iff₀ hd2, hn'eq]
    have hS2 : S ≤ 2 * nr := by rw [hS]; linarith only [hKa_le]
    have hMr0 : 0 ≤ Mr := zero_le_one.trans hMr1
    have p1 : Mr * ur * S ≤ Mr * (K * dl) * (2 * nr) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hud hMr0) hS2 hSpos.le (mul_nonneg hMr0 hKdl0)
    linarith only [p1, hq, hud, hKdl0]
  have hyS : (y1 + y2) * S ≤ (K + 1) * a := by
    linarith only [hy1S, hy2S, ha1]
  have hny : nr ≤ S * (1 - (y1 + y2)) := by
    linarith only [hS, hyS]
  have hexp : Real.exp (y1 + y2) * (1 - (y1 + y2)) ≤ 1 := by
    have h0 : 1 - (y1 + y2) ≤ Real.exp (-(y1 + y2)) := by
      rw [sub_eq_add_neg, add_comm 1]
      exact Real.add_one_le_exp (-(y1 + y2))
    calc Real.exp (y1 + y2) * (1 - (y1 + y2)) ≤ Real.exp (y1 + y2) * Real.exp (-(y1 + y2)) :=
          mul_le_mul_of_nonneg_left h0 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hmain : nr * Real.exp (y1 + y2) ≤ S := by
    calc nr * Real.exp (y1 + y2) ≤ (S * (1 - (y1 + y2))) * Real.exp (y1 + y2) :=
          mul_le_mul_of_nonneg_right hny (Real.exp_pos _).le
      _ = S * (Real.exp (y1 + y2) * (1 - (y1 + y2))) := mul_right_comm _ _ _ |>.trans (mul_assoc _ _ _)
      _ ≤ S * 1 := mul_le_mul_of_nonneg_left hexp hSpos.le
      _ = S := mul_one S
  have hX0 : 0 ≤ (cardUX D N (n - deF) (n' - u) : ℝ) := Nat.cast_nonneg _
  have hprod : (cardUX D N n n' : ℝ) ≤
      (cardUX D N (n - deF) (n' - u) : ℝ) * Real.exp (y1 + y2) := by
    rw [hc1, hc2, Real.exp_add]
    calc _ ≤ ((((n - deF + (D + 1)).choose (D + 1) : ℕ) : ℝ) * Real.exp y1) *
          ((((n' - u + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) : ℕ) : ℝ) * Real.exp y2) :=
          mul_le_mul hA hB (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
      _ = _ := mul_mul_mul_comm _ _ _ _
  have hnr0 : 0 ≤ nr := zero_le_one.trans hnr1
  calc (n : ℝ) * cardUX D N n n' ≤ nr * ((cardUX D N (n - deF) (n' - u) : ℝ) * Real.exp (y1 + y2)) :=
        mul_le_mul_of_nonneg_left hprod hnr0
    _ = (cardUX D N (n - deF) (n' - u) : ℝ) * (nr * Real.exp (y1 + y2)) := mul_left_comm _ _ _
    _ ≤ (cardUX D N (n - deF) (n' - u) : ℝ) * S := mul_le_mul_of_nonneg_left hmain hX0
    _ = ((n : ℝ) + (D + 2) * deF) * cardUX D N (n - deF) (n' - u) := by
        rw [hS, hK, ha, hnr]; push_cast; ring

end ReciprocityTheory.ChartRestriction.G.T0
