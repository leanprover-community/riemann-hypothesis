module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KTypeCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ClusterNum

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq abs_sig)
open PI.UpqRep

theorem numKG : NumKG := by
  intro n ε γ lev ν B C hG hB hBn hC _ hdom hn
  set X := xv ε γ with hX
  set κ := X - rhoC ε - wt B with hκ
  set μ := X - wt B - wt C with hμ
  obtain ⟨hXa, -, hgap⟩ := hG
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  have hκw := sorted_weight_eq_of_norm_eq ε κ μ ν C hC w hw hs (hdom w hw)
    (fun a => by simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring) hn
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => (hBn _ h2).1 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hcd' : c < d := hcd
  have hne : t c d = -1 := by
    have h1 : ¬ε c = ε d := (hBn _ hi).1
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have hgcd : Lc n ≤ X c - X d := hgap c d (hBn _ hi).2

  have p1 := pair_eq t ta X
  have p2 := pair_eq sig sig_anti X
  have hD : ∀ a b, 0 ≤ sig a b * (X a - X b) - t a b * (X a - X b) := fun a b => by
    rw [sig_mul hXa, sub_nonneg]
    exact (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (tb' a b))
  have hDcd : 2 * Lc n ≤ sig c d * (X c - X d) - t c d * (X c - X d) := by
    rw [hne, show sig c d = 1 by simp [sig, hcd']]
    linarith
  have hsum : ∑ a, ∑ b, t a b * (X a - X b) + 2 * Lc n ≤ ∑ a, ∑ b, sig a b * (X a - X b) := by
    have h1 : sig c d * (X c - X d) - t c d * (X c - X d) ≤
        ∑ a, ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)) :=
      (Finset.single_le_sum (f := fun b => sig c b * (X c - X b) - t c b * (X c - X b))
        (fun b _ => hD c b) (mem_univ d)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)))
        (fun a _ => Finset.sum_nonneg fun b _ => hD a b) (mem_univ c))
    simp only [Finset.sum_sub_distrib] at h1
    linarith
  have hy : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) := fun a => by
    have h1 := hκw (w.symm a)
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    have ts : ∑ b, t a b = ∑ b, sig a b - ∑ b, sc ε a b - 2 * ∑ b, (ind B a b - ind B b a) +
        ∑ b, sc ε (w.symm a) (w.symm b) := by
      simp only [t]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b),
        Finset.sum_sub_distrib (f := fun b => sig a b), ← Finset.mul_sum]
    simp only [hκ, Equiv.apply_symm_apply, Pi.sub_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ts]
    linarith
  have hY : ∀ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := fun a => by
    have e : (∑ b, t a b) / 2 - (∑ b, sig a b) / 2 = (∑ b, (t a b - sig a b)) / 2 := by
      rw [Finset.sum_sub_distrib]; ring
    have h2 : |∑ b, (t a b - sig a b)| ≤ 2 * (n : ℝ) := by
      calc _ ≤ ∑ b, |t a b - sig a b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b : Fin n, (2 : ℝ) := Finset.sum_le_sum fun b _ => by
            have := abs_sub (t a b) (sig a b)
            linarith [tb' a b, abs_sig a b]
        _ = 2 * (n : ℝ) := by simp [mul_comm]
    rw [e, div_pow]
    have h3 : (∑ b, (t a b - sig a b)) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    nlinarith
  have g1 : vNormSq ε ν = ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 := by
    unfold vNormSq nsq dot
    rw [← Equiv.sum_comp w.symm]
    exact Finset.sum_congr rfl fun a _ => by rw [hy, sq]
  have g2 : vNormSq ε γ = ∑ a, X a ^ 2 := by
    unfold vNormSq nsq dot
    exact Finset.sum_congr rfl fun a _ => (sq _).symm
  have g3 : ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 = ∑ a, X a ^ 2 +
      (2 * ∑ a, X a * ((∑ b, t a b) / 2) - 2 * ∑ a, X a * ((∑ b, sig a b) / 2)) +
      ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have g4 : ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc _ ≤ ∑ _a : Fin n, (n : ℝ) ^ 2 := Finset.sum_le_sum fun a _ => hY a
      _ = (n : ℝ) ^ 3 := by simp; ring
  have g5 : (n : ℝ) ^ 3 < Lc n := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold Lc
    nlinarith [pow_le_pow_left₀ h0 (by linarith : (n : ℝ) ≤ n + 1) 3, pow_pos (by linarith : (0 : ℝ) < n + 1) 3]
  rw [g1, g2, g3]
  linarith

end GlobalTheory.CompanionTheory.ClusterNum
