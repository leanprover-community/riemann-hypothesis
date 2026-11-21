import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.LineModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mem_of_aeval (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

theorem eval_map_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def]; rfl

theorem ptsOver_complex (P : Ideal (MRing ι)) : ptsOver ℂ P = mcPts P := by
  ext z
  simp only [ptsOver, mcPts, Set.mem_setOf_eq, eval_map_eq]

theorem hasVal_unique (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {w w' : 𝕜}
    (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, e1, n1, v1⟩ := h
  obtain ⟨dg', dh', g', h', hg', hh', hd', e1', n1', v1'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have := hd k; have := hd' k
    simp only [Pi.add_apply]; omega
  have hom : IsMultiHomog (g * h' + -(g' * h)) (dg + dh') :=
    ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg (hdeg ▸ ProjLine.mhMul hg' hh))
  have h0 := hz.2 _ (mem_of_aeval y hom (by simp only [map_add, map_neg, map_mul, e1, e1']; ring))
  simp only [map_add, map_neg, map_mul, v1, v1'] at h0
  have : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero n1 n1'))

theorem hasVal_form (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜) :
    HasVal y (fun k => (d k : ℤ)) (aeval y g) z (aeval z g) :=
  ⟨d, 0, g, 1, hg, ProjLine.isMultiHomog_one, fun k => by simp, by simp, by simp, by simp⟩



theorem liesOver_rat [CharZero Ω] (y : (Σ k, ι k) → Ω) (sg : ℚ →+* ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : LiesOver y sg z := by
  intro d g h θ hg hh e
  have hC : ∀ r : ℤ, IsMultiHomog (C r : MRing ι) 0 := by
    classical
    intro r m hm k
    rw [mem_support_iff, coeff_C] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  have hom : IsMultiHomog (C (θ.den : ℤ) * g + -(C θ.num * h)) (0 + d) :=
    ProjLine.mhAdd (ProjLine.mhMul (hC _) hg) (ProjLine.mhNeg (ProjLine.mhMul (hC _) hh))
  have h0 := hz.2 _ (mem_of_aeval y hom (by
    simp only [map_add, map_neg, map_mul, e, eq_intCast, map_intCast, map_natCast, eq_ratCast,
      Int.cast_natCast]
    have : (θ.den : Ω) * (θ : Ω) = θ.num := by exact_mod_cast Rat.den_mul_eq_num θ
    rw [← this]; ring))
  rw [eval_map_eq] at h0
  rw [eval_map_eq, eval_map_eq]
  simp only [map_add, map_neg, map_mul, eq_intCast, map_intCast, map_natCast, Int.cast_natCast] at h0
  have h1 : (θ.den : ℂ) * (θ : ℂ) = θ.num := by exact_mod_cast Rat.den_mul_eq_num θ
  have h2 : (θ.den : ℂ) ≠ 0 := by exact_mod_cast θ.den_ne_zero
  rw [eq_ratCast]
  apply mul_left_cancel₀ h2
  rw [← mul_assoc, h1]
  linear_combination h0

end General

open ProjLine

theorem isModelOver_line : IsModelOver (ι := GlobalTheory (Fin 2)) y ℚ 1 where
  one_le := le_rfl
  arith := isArithVar_y'
  bir := birational_y
  uniq z hz := ⟨Rat.castHom ℂ, liesOver_rat y _ hz, fun _ _ => Subsingleton.elim _ _⟩


theorem coord_le_fs (z : Ix (Fin 2) → ℂ) (p : Ix (Fin 2)) : ‖z p‖ ≤ fsLine1.h z :=
  PiLp.norm_apply_le (WithLp.toLp 2 z) p


def triv : HermLine (GlobalTheory (Fin 2)) := HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)



end GlobalTheory.CompanionTheory.Ar.Small.LineModel
