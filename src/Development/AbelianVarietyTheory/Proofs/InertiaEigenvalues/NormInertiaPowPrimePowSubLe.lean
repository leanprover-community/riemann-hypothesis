module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowIndexLeOfFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
