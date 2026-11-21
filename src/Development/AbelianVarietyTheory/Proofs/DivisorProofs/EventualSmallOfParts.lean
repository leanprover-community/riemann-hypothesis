import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaLimitStatement
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem four_f_r_le_k_pow_eight (R : Ranks) : 4 * R.f * R.r ≤ R.k ^ 8 := by
  have hf : R.f ≤ R.k := by
    unfold Ranks.f Ranks.n
    exact R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hr : R.r ≤ 2 * R.k := by
    unfold Ranks.r
    omega
  have hk : 2 ≤ R.k := by omega
  have h6 : 8 ≤ R.k ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hk 6)
  calc 4 * R.f * R.r ≤ 4 * R.k * (2 * R.k) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hr
    _ = 8 * R.k ^ 2 := by ring
    _ ≤ R.k ^ 6 * R.k ^ 2 := Nat.mul_le_mul_right _ h6
    _ = R.k ^ 8 := by ring

theorem four_f_r_le_min_g_of_sizeG {D : D7} (L : SizeData₂ D) (h : SizeG L) : Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D := by
  have hb : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _)
  have key : ∀ i : Fin 2, 4 * D.R.f * D.R.r ≤ D.host.g i := by
    intro i
    have h1 := (h i i).1
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
      pow_le_pow_left₀ hk (le_mul_of_one_le_right hk hb) 8
    have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
    exact (four_f_r_le_k_pow_eight D.R).trans h3
  unfold Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound
  exact le_min (key 0) (key 1)

theorem four_f_r_le_min_g_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x →
    ∀ i : Fm.Ix x, Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound (Fm.D x i) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := Fm.sizes x hx i
  exact four_f_r_le_min_g_of_sizeG _ hG

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.Ind

theorem small_along : ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), AtAll PSeeEx 𝒜 σ → AtAll PPA 𝒜 σ → EvWC (fun _ => True) Small 𝒜 σ := by
  intro 𝒜 σ hS hP
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm CH hw _ _ => ⟨0, le_refl _, fun C _ => ?_⟩
  obtain ⟨x0, hx0⟩ := GlobalTheory.four_f_r_le_min_g_family _ Fm
  refine ⟨x0, fun x hx hx0' i => ?_⟩
  have hA := hx0 x hx0' hx i
  have hs := hS Fm (w3_a hw) x hx i
  have hp := hP Fm (w3_a hw) x hx i
  refine ⟨fun w hw1 => ((σ Fm (w3_a hw) x hx i).muDef C CH).2.2.2 w |>.2 hw1, ?_, ?_⟩
  · exact GlobalTheory.T.indefinite_scale_theta_limit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  · exact GlobalTheory.T.indefinite_scale_theta_degree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Fm.D x i).tcLL hA (σ Fm (w3_a hw) x hx i).ok1 hp.1 C CH
end GlobalTheory.Fc.Ind
end
