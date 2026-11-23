module

import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetHeightBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormDetLeHeightPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormVecMulGeOfHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.Reduction
import GroundTheory.AutomorphicForms.ReductionCore
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace UpperTheory.V.Fb

private theorem box {n d : ℕ} (hd : d ≠ 0) {r : Fin (n + 1) → ℝ} (hr : ∀ i, 0 < r i) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (h1 : ∀ i, 1 ≤ A * r i ^ d) (h2 : (∏ i, r i) ^ d ≤ B) (i : Fin (n + 1)) :
    r i ≤ B * A ^ (n + 1) ∧ (r i)⁻¹ ≤ B * A ^ (n + 1) := by
  have hL : 1 ≤ B * A ^ (n + 1) := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hA)
  have key : ∀ x : ℝ, x ^ d ≤ B * A ^ (n + 1) → x ≤ B * A ^ (n + 1) := fun x hx =>
    le_of_pow_le_pow_left₀ hd (by positivity) (hx.trans (le_self_pow₀ hL hd))
  refine ⟨key _ ?_, key _ ?_⟩
  · have h3 : 1 ≤ ∏ j : Fin n, A * r (i.succAbove j) ^ d :=
      Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun j _ => h1 _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow] at h3
    rw [Fin.prod_univ_succAbove _ i, mul_pow] at h2
    have h4 := pow_pos (hr i) d
    calc r i ^ d ≤ r i ^ d * (A ^ n * (∏ j : Fin n, r (i.succAbove j)) ^ d) := le_mul_of_one_le_right h4.le h3
      _ = (r i ^ d * (∏ j : Fin n, r (i.succAbove j)) ^ d) * A ^ n := by ring
      _ ≤ B * A ^ (n + 1) := mul_le_mul h2 (pow_le_pow_right₀ hA n.le_succ) (by positivity) (by positivity)
  · rw [inv_pow]
    refine ((inv_le_iff_one_le_mul₀ (pow_pos (hr i) d)).2 (h1 i)).trans ?_
    exact (le_self_pow₀ hA n.succ_ne_zero).trans (le_mul_of_one_le_left (by positivity) hB)

variable {K : Type} [Field K] [NumberField K]

private theorem lastRow {m : ℕ} {ω : Set (AdelicGLn.AdelicGL K (m + 1))} (hω : IsCompact ω)
    (hB : ω ⊆ (adelicBorel (K := K) (n := m + 1) : Set (AdelicGLn.AdelicGL K (m + 1)))) :
    ∃ P : ℝ, 0 < P ∧ ∀ b ∈ ω, ∀ (r : Fin (m + 1) → ℝ) (hr : ∀ i, 0 < r i),
      height (b * diagUnits (m + 1) fun i => posIdele (K := K) (r i) (hr i)) (Pi.single (Fin.last m) 1) ≤
        P * r (Fin.last m) ^ Module.finrank ℚ K := by
  obtain ⟨P, hP, h⟩ := exists_adelicNorm_vecMul_le_mul hω
  refine ⟨P, hP, fun b hb r hr => ?_⟩
  obtain ⟨u, hu⟩ := isUnit_apply_self_of_mem_adelicBorel (hB hb) (Fin.last m)
  have e : Pi.single (Fin.last m) 1 ᵥ* b.val = Pi.single (Fin.last m) u.val := by
    rw [single_one_vecMul]
    funext j
    rcases (Fin.le_last j).eq_or_lt with rfl | hj
    · simp [Matrix.row, hu]
    · rw [Pi.single_eq_of_ne hj.ne]
      exact hB hb hj
  have h1 := h b hb _ (hasFiniteContent_single_one (K := K) (Fin.last m))
  rw [e, adelicNorm_single_one, mul_one, adelicNorm_single_units] at h1
  rw [height, Units.val_mul, ← vecMul_vecMul, ratVec_single_one, e, coe_diagUnits, single_vecMul_diagonal,
    ← Units.val_mul, adelicNorm_single_units, map_mul, Positive.val_mul, ideleModule_posIdele]
  exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (hr _).le _)

theorem siegelHeight : SiegelHeight := by
  apply UpperTheory.siegelSet_height_bound <;> assumption

end UpperTheory.V.Fb
