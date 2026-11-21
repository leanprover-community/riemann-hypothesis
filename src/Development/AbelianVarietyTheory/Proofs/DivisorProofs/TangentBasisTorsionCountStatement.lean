import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

namespace GlobalTheory.HTLevelSq

theorem mem_latHT_iff_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) ∧ (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ∀ i, ‖(p : ℂ_[p]) * a i‖ ≤ 1) := by
  intro E _ _ _ H X _ t hX p hp x g e he N c h hAll hdl
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := PadicComplexHost.norm_p p
  have hx : ∀ x' : Sp ↥(intO ℂ_[p]) ⟶ X,
      spMap (intO ℂ_[p]).subtype ≫ x' = spMap (intO ℂ_[p]).subtype ≫ x → x' = x :=
    fun x' h' => GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' h'
  have hc1 : ∀ c₁ : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c₁ e (h j) := fun c₁ => by
    obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t ℂ_[p] x (p ^ 1) (p ^ 2) (pow_ne_zero _ hp.out.ne_zero)
      (pow_dvd_pow _ (by norm_num)) c₁
    obtain ⟨j, hj⟩ := hAll c'
    exact ⟨j, GlobalTheory.HTLevel.dlog_down (by norm_num) c' c₁ hc' he.1 (GlobalTheory.HTMap.dlog_congr he.1 hj (hdl j))⟩
  have hj1 : ∀ j, ∃ c₁ : TorsChar t x (p ^ 1), DlogIs t p 1 c₁ e (h j) := fun j =>
    ⟨GlobalTheory.HTLevel.res (pow_dvd_pow p (by norm_num : 1 ≤ 2)) (c j),
      GlobalTheory.HTLevel.dlog_down (by norm_num : 1 ≤ 2) (c j) (GlobalTheory.HTLevel.res (pow_dvd_pow p (by norm_num : 1 ≤ 2)) (c j))
        (fun _ _ _ _ _ _ => rfl) he.1 (hdl j)⟩
  have L1 := fun a w hw => GlobalTheory.HTLevel.mem_latHT_iff GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn x hx g e he N h
    hc1 hj1 a w hw
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  have step : ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w →
      (∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) → (∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1) →
      w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) := by
    intro a w hw h1 h2
    let b : Fin g → ↥(intO ℂ_[p]) := fun i => ⟨(p : ℂ_[p]) ^ 2 * a i, h2 i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    refine ⟨x, rfl, 2, vO, hv, ?_, fun k c₀ w' hw' => ?_⟩
    · exact Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hbv) (Guard.comb_smul heC hw _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 0}) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
      rw [Subsingleton.elim (TrivSqZeroExt.snd _) 0]
      exact Ideal.zero_mem _
    obtain ⟨j, D, hD, hδ⟩ : ∃ j, ∃ D : Fin g → ↥(intO ℂ_[p]), DlogIs t p k c₀ e D ∧
        ∀ i, D i - h j i ∈ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2} := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        obtain ⟨j, hj⟩ := hc1 c₀
        exact ⟨j, h j, hj, fun i => by simp⟩
      · obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c₀ g e he.1
        obtain ⟨j, hj⟩ := hAll (GlobalTheory.HTLevel.res (pow_dvd_pow p hk2) c₀)
        exact ⟨j, D, hD, (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p 2 _ g e he.1).2 D (h j)
          (GlobalTheory.HTLevel.dlog_down hk2 c₀ (GlobalTheory.HTLevel.res (pow_dvd_pow p hk2) c₀) (fun _ _ _ _ _ _ => rfl) he.1 hD) (GlobalTheory.HTMap.dlog_congr he.1 hj (hdl j))⟩
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    let s : ↥(intO ℂ_[p]) := ⟨∑ i, (h j i : ℂ_[p]) * a i, h1 j⟩
    have h3 : ∑ i, D i * b i = (s + ∑ i, δ i * b i) * (p : ↥(intO ℂ_[p])) ^ 2 := by
      apply (intO ℂ_[p]).subtype_injective
      simp only [map_mul, map_pow, map_natCast, map_sum, map_add, Subring.subtype_apply, s, b]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO ℂ_[p]).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (-(p : ℂ_[p]) ^ 2 * a i) * this
    rw [hD b vO hbv w' hw', h3, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  intro a w hw
  refine ⟨⟨fun hL => ((L1 a w hw).1 hL).1, fun hd => ?_⟩, fun hL => ((L1 a w hw).1 hL).2⟩
  by_cases hbig : ∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1
  · exact step a w hw hd hbig
  exfalso
  push_neg at hbig
  obtain ⟨i₀, hi₀⟩ := hbig
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖a i‖) ⟨i₀, Finset.mem_univ _⟩
  have hai : 1 < ‖(p : ℂ_[p]) ^ 2 * a i‖ := by
    refine lt_of_lt_of_le hi₀ ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hi i₀ (Finset.mem_univ _)) (norm_nonneg _)
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have ha0 : a i ≠ 0 := fun h0 => by rw [h0, mul_zero, norm_zero] at hai; linarith
  have hl1 : ‖((p : ℂ_[p]) ^ 2 * a i)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hai.le
  have hlw := Guard.comb_smul heC hw ((p : ℂ_[p]) ^ 2 * a i)⁻¹
  have hd' : ∀ j, ‖∑ k, (h j k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun j => by
    have e2 : ∑ k, (h j k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) =
        ((p : ℂ_[p]) ^ 2 * a i)⁻¹ * ∑ k, (h j k : ℂ_[p]) * a k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e2, norm_mul]
    exact mul_le_one₀ hl1 (norm_nonneg _) (hd j)
  have hb' : ∀ k, ‖(p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun k => by
    have e3 : (p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) = a k / a i := by field_simp
    rw [e3, norm_div]
    exact div_le_one_of_le₀ (hi k (Finset.mem_univ _)) (norm_nonneg _)
  have hmem := step _ _ hlw hd' hb'
  have h4 := ((L1 _ _ hlw).1 hmem).2 i
  have e1 : (p : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a i) = (p : ℂ_[p])⁻¹ := by field_simp
  rw [e1, norm_inv, hn, inv_inv] at h4
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  linarith

end GlobalTheory.HTLevelSq
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_torsion_chars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) ∧ (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ∀ i, ‖(p : ℂ_[p]) * a i‖ ≤ 1) := by
  first | exact @GlobalTheory.HTLevelSq.mem_latHT_iff_sq | exact GlobalTheory.HTLevelSq.mem_latHT_iff_sq | (intros; apply GlobalTheory.HTLevelSq.mem_latHT_iff_sq <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.DlogClose

theorem dlog_sub_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (c : TorsChar t x (p ^ 2)) (h : Fin g → ↥(intO ℂ_[p])) (h' : Fin g' → ↥(intO ℂ_[p])), DlogIs t p 2 c e h → DlogIs t p 2 c e' h' → ∀ (a : Fin g → ℂ_[p]) (a' : Fin g' → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) a' w → w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ‖∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i‖ < 1 := by
  intro E _ _ _ H X _ t hX p hp x g g' e e' he he' c h h' hD hD' a a' w hw hw' hL
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  obtain ⟨x', hx', vO, hv, hs⟩ := GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn x
    (fun x' hx' => GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' hx') w hL p (by
      rw [hn, ← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
      rw [div_le_one (by linarith)]
      linarith)
  obtain rfl := GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' hx'
  obtain ⟨b, hbv, hb⟩ := GlobalTheory.HTLevel.coords he hw _ hv hs
  obtain ⟨b', hbv', hb'⟩ := GlobalTheory.HTLevel.coords he' hw' _ hv hs
  obtain ⟨u, hu⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2}) hv
  have h1 := hD b vO hbv u hu
  have h2 := hD' b' vO hbv' u hu
  rw [h1, Ideal.Quotient.eq] at h2
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h2
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h3 : ∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i = (r : ℂ_[p]) * p := by
    apply mul_left_cancel₀ hp0
    have := congrArg (intO ℂ_[p]).subtype hr
    simp only [map_mul, map_pow, map_natCast, map_sum, map_sub, Subring.subtype_apply, hb, hb'] at this
    have e1 : ∑ i, (h i : ℂ_[p]) * ((p : ℂ_[p]) * a i) = (p : ℂ_[p]) * ∑ i, (h i : ℂ_[p]) * a i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (h' i : ℂ_[p]) * ((p : ℂ_[p]) * a' i) = (p : ℂ_[p]) * ∑ i, (h' i : ℂ_[p]) * a' i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at this
    linear_combination (-1 : ℂ_[p]) * this
  rw [h3, norm_mul, hn]
  have hr1 : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have hpi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  calc ‖(r : ℂ_[p])‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ := by gcongr
    _ < 1 := by rw [_root_.one_mul]; exact hpi

end GlobalTheory.HtGen.DlogClose
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_change_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (c : TorsChar t x (p ^ 2)) (h : Fin g → ↥(intO ℂ_[p])) (h' : Fin g' → ↥(intO ℂ_[p])), DlogIs t p 2 c e h → DlogIs t p 2 c e' h' → ∀ (a : Fin g → ℂ_[p]) (a' : Fin g' → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) a' w → w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ‖∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i‖ < 1 := by
  atlas_forward_decl GlobalTheory.HtGen.DlogClose.dlog_sub_norm_lt_one
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem detClose_norm_prod_sub_lt {C : Type} [NormedField C] [IsUltrametricDist C] {ι : Type}
    (s : Finset ι) (f g : ι → C) (hf : ∀ i, ‖f i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ < 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ < 1 := by
  classical
  have hg : ∀ i, ‖g i‖ ≤ 1 := fun i => by
    have : g i = f i + -(f i - g i) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf i) (by rw [norm_neg]; exact (hfg i).le))
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ 1 * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ :=
            mul_le_mul_of_nonneg_right (hf a) (norm_nonneg _)
        _ < 1 := by simpa using ih
    · rw [norm_mul, norm_prod]
      calc ‖f a - g a‖ * ∏ i ∈ s, ‖g i‖ ≤ ‖f a - g a‖ * 1 :=
            mul_le_mul_of_nonneg_left (Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hg i))
              (norm_nonneg _)
        _ < 1 := by simpa using hfg a

theorem detClose_norm_sum_lt {C : Type} [NormedField C] [IsUltrametricDist C] {ι : Type}
    (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem detClose_norm_det_sub_lt {C : Type} [NormedField C] [IsUltrametricDist C] {k : ℕ}
    (B B' : Matrix (Fin k) (Fin k) C) (hB : ∀ i j, ‖B i j‖ ≤ 1)
    (hBB : ∀ i j, ‖B i j - B' i j‖ < 1) : ‖B.det - B'.det‖ < 1 := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  apply detClose_norm_sum_lt
  intro σ _
  rw [← mul_sub, norm_mul]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : C)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact detClose_norm_prod_sub_lt _ _ _ (fun i => hB _ _) (fun i => hBB _ _)

theorem det_sub_lt_of_close_on_unitBall : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (J : Type) (k : ℕ) (P P' : J → Fin k → C) (N : ℝ), 0 < N → (∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ ≤ N) → (∃ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ = N) → (∀ cf : Fin k → C, (∀ j, ‖∑ l, cf l * P j l‖ ≤ 1) → ∀ j, ‖∑ l, cf l * (P j l - P' j l)‖ < 1) → ∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det - (Matrix.of fun r l => P' (σ r) l).det‖ < N := by
  intro C _ _ J k P P' N hN hle ⟨σ₀, hσ₀⟩ hclose σ
  classical
  set A : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P (σ₀ r) l with hA
  have hdetA : A.det ≠ 0 := by
    intro h; rw [h, norm_zero] at hσ₀; linarith
  set Q := A⁻¹ with hQ

  have hcol : ∀ (c : Fin k) (j : J), ‖∑ l, Q l c * P j l‖ ≤ 1 := by
    intro c j
    have h1 : ∑ l, A.adjugate l c * P j l = (A.updateRow c (P j)).det := by
      rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
        ← Matrix.adjugate_transpose]
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    have h2 : A.updateRow c (P j) = Matrix.of fun r l => P (Function.update σ₀ c j r) l := by
      ext r l
      by_cases hr : r = c
      · subst hr; simp [Matrix.updateRow_apply]
      · simp [Matrix.updateRow_apply, hr, Function.update_of_ne hr, hA]
    have h3 : ∑ l, Q l c * P j l = (A.det)⁻¹ * ∑ l, A.adjugate l c * P j l := by
      rw [hQ, Matrix.inv_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, mul_assoc]
    rw [h3, h1, h2, norm_mul, norm_inv, hσ₀]
    rw [inv_mul_le_iff₀ hN, mul_one]
    exact hle _
  set M : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P (σ r) l
  set M' : Matrix (Fin k) (Fin k) C := Matrix.of fun r l => P' (σ r) l
  have hB : ∀ r c, ‖(M * Q) r c‖ ≤ 1 := by
    intro r c
    rw [Matrix.mul_apply]
    simpa [M, mul_comm] using hcol c (σ r)
  have hBB : ∀ r c, ‖(M * Q) r c - (M' * Q) r c‖ < 1 := by
    intro r c
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    have := hclose (fun l => Q l c) (fun j => hcol c j) (σ r)
    convert this using 2
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [M, M']; ring
  have hkey := detClose_norm_det_sub_lt (M * Q) (M' * Q) hB hBB
  have hQA : Q.det * A.det = 1 := by
    rw [hQ, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_mul_cancel₀ hdetA]
  have e : M.det - M'.det = ((M * Q).det - (M' * Q).det) * A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, sub_mul, mul_assoc, mul_assoc, hQA, mul_one, mul_one]
  show ‖M.det - M'.det‖ < N
  rw [e, norm_mul, hσ₀]
  calc ‖(M * Q).det - (M' * Q).det‖ * N < 1 * N := mul_lt_mul_of_pos_right hkey hN
    _ = N := one_mul N

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_perturbation_bound : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] (J : Type) (k : ℕ) (P P' : J → Fin k → C) (N : ℝ), 0 < N → (∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ ≤ N) → (∃ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det‖ = N) → (∀ cf : Fin k → C, (∀ j, ‖∑ l, cf l * P j l‖ ≤ 1) → ∀ j, ‖∑ l, cf l * (P j l - P' j l)‖ < 1) → ∀ σ : Fin k → J, ‖(Matrix.of fun r l => P (σ r) l).det - (Matrix.of fun r l => P' (σ r) l).det‖ < N := by
  atlas_forward_decl GlobalTheory.det_sub_lt_of_close_on_unitBall
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.PointDet

attribute [local instance] Over.cartesianMonoidalCategory

theorem pairDet_eq_sum {C J : Type} [CommRing C] {g m k : ℕ} (h : J → Fin g → C) (a : Fin m → Fin g → C)
    (hk : k ≤ m) (σ : Fin k → J) :
    pairDet h a hk σ = ∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s := by
  classical
  have hM : (Matrix.of fun r l : Fin k => ∑ i, h (σ r) i * a (Fin.castLE hk l) i) =
      fun r => ∑ i, h (σ r) i • (fun l : Fin k => a (Fin.castLE hk l) i) := by
    ext r l; simp [Finset.sum_apply]
  unfold pairDet
  rw [hM]
  change Matrix.detRowAlternating.toMultilinearMap _ = _
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  congr 1
  unfold minor
  rw [← Matrix.det_transpose]
  rfl

theorem sum_extend {C : Type} [CommRing C] {m k : ℕ} (hk : k ≤ m) (cf : Fin k → C) (f : Fin m → C) :
    ∑ l', (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0) l' * f l' =
      ∑ l : Fin k, cf l * f (Fin.castLE hk l) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ (fun l' hl' => ?_) (fun l => ?_)
  · have : ¬ (l' : ℕ) < k := fun hl => hl' ⟨⟨l', hl⟩, Fin.ext rfl⟩
    simp [this]
  · simp

theorem sum_comb_extend {C : Type} [CommRing C] {g m k : ℕ} (hk : k ≤ m) (cf : Fin k → C) (hh : Fin g → C)
    (a : Fin m → Fin g → C) :
    ∑ i, hh i * (∑ l', (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0) l' • a l') i =
      ∑ l : Fin k, cf l * ∑ i, hh i * a (Fin.castLE hk l) i := by
  rw [← sum_extend hk cf (fun l' => ∑ i, hh i * a l' i)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun i _ => by ring

theorem pairDet_htLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])) (h' : Fin N → Fin g' → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → (∀ j, DlogIs t p 2 (c j) e' (h' j)) → ∀ (m k : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]) (a' : Fin m → Fin g' → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (a' l) (u l)) → ∀ ν : ℝ, ν = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u (Fin.castLE hk l) → (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u l) ∧ (∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν) ∧ (∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν) ∧ ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ - pairDet (fun j i => (h' j i : ℂ_[p])) a' hk σ‖ < ν := by
  intro E _ _ _ H X _ t hX p _ x g g' e e' he he' N c h h' hall hdl hdl' m k hk u a a' ha hu hu' ν hν0
  set xC := spMap (intO ℂ_[p]).subtype ≫ x with hxC
  have heC := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he
  have hlat := fun b w hw => GlobalTheory.T.tangent_basis_torsion_chars E H X t hX p x g e he N c h hall hdl b w hw
  have hut : ∀ l, IsTanAtG t xC (u l) := fun l => GlobalTheory.LineNorm.Chart.comb_tan heC.1 (hu l)
  have hgr := fun l => GlobalTheory.LineNorm.WedgeMax.grNorm_eq t heC.1
    (P := fun b => ∀ j, ‖∑ i, (h j i : ℂ_[p]) * b i‖ ≤ 1) (fun b w hw => (hlat b w hw).1) hu l
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hker : ∀ cc : Fin g → ℂ_[p], (∀ j, ∑ i, (h j i : ℂ_[p]) * cc i = 0) → cc = 0 := by
    intro cc hcc
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hi' : cc i ≠ 0 := by simpa using hi
    obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm ℂ_[p]
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t heC.1 ((y / ((p : ℂ_[p]) * cc i)) • cc)
    have hmem := (hlat _ w hw).1.2 fun j => by
      have : ∑ i', (h j i' : ℂ_[p]) * ((y / ((p : ℂ_[p]) * cc i)) • cc) i' =
          (y / ((p : ℂ_[p]) * cc i)) * ∑ i', (h j i' : ℂ_[p]) * cc i' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this, hcc j]; simp
    have h1 := (hlat _ w hw).2 hmem i
    have : (p : ℂ_[p]) * ((y / ((p : ℂ_[p]) * cc i)) • cc) i = y := by
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      try ring
    rw [this] at h1
    linarith
  obtain ⟨hpos, hprod⟩ := GlobalTheory.T.successive_minima_positive_norms ℂ_[p] g (Fin N) (fun j i => (h j i : ℂ_[p])) hker m a ha _ hgr
  have hν : ν = ⨆ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ := by
    rw [hν0, hprod k hk]
    congr 1
    ext σ
    rw [pairDet_eq_sum]
  have hνpos : 0 < ν := hν0 ▸ Finset.prod_pos fun l _ => hpos _
  have hne : Nonempty (Fin k → Fin N) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at hν
    linarith
  have hle : ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν := fun σ =>
    hν ▸ le_ciSup (f := fun σ => ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖) (Finite.bddAbove_range _) σ
  have hex : ∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν := hν ▸ exists_eq_ciSup_of_finite
  refine ⟨hpos, hle, hex, fun σ => ?_⟩
  have hclose : ∀ cf : Fin k → ℂ_[p], (∀ j, ‖∑ l, cf l * ∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i‖ ≤ 1) →
      ∀ j, ‖∑ l, cf l * ((∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i) -
        ∑ i, (h' j i : ℂ_[p]) * a' (Fin.castLE hk l) i)‖ < 1 := by
    intro cf hcf j
    obtain ⟨w, -, hw⟩ := GlobalTheory.LineNorm.WedgeMax.exists_comb t hut
      (fun l' : Fin m => if hl : (l' : ℕ) < k then cf ⟨l', hl⟩ else 0)
    have hwe := GlobalTheory.LineNorm.Chart.comb_comb heC.1 hu hw
    have hwe' := GlobalTheory.LineNorm.Chart.comb_comb (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t (intO ℂ_[p]).subtype he').1 hu' hw
    have hmem := (hlat _ w hwe).1.2 fun j' => by
      rw [sum_comb_extend]; exact hcf j'
    have h1 := GlobalTheory.T.tangent_basis_change_torsion E H X t hX p x g g' e e' he he' (c j) (h j) (h' j) (hdl j) (hdl' j) _ _ w hwe hwe' hmem
    rw [sum_comb_extend, sum_comb_extend, ← Finset.sum_sub_distrib] at h1
    simpa only [mul_sub] using h1
  exact GlobalTheory.T.determinant_perturbation_bound ℂ_[p] (Fin N) k (fun j l => ∑ i, (h j i : ℂ_[p]) * a (Fin.castLE hk l) i)
    (fun j l => ∑ i, (h' j i : ℂ_[p]) * a' (Fin.castLE hk l) i) ν hνpos hle hex hclose σ

end GlobalTheory.HtGen.PointDet
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairDet_norm_le_attained_and_sub_norm_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])) (h' : Fin N → Fin g' → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → (∀ j, DlogIs t p 2 (c j) e' (h' j)) → ∀ (m k : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]) (a' : Fin m → Fin g' → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) (a l) (u l)) → (∀ l, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) (a' l) (u l)) → ∀ ν : ℝ, ν = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u (Fin.castLE hk l) → (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ℂ_[p]).subtype ≫ x) (latHT t p (spMap (intO ℂ_[p]).subtype ≫ x)) u l) ∧ (∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ ≤ ν) ∧ (∃ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ‖ = ν) ∧ ∀ σ : Fin k → Fin N, ‖pairDet (fun j i => (h j i : ℂ_[p])) a hk σ - pairDet (fun j i => (h' j i : ℂ_[p])) a' hk σ‖ < ν := by
  first | exact @GlobalTheory.HtGen.PointDet.pairDet_htLattice | exact GlobalTheory.HtGen.PointDet.pairDet_htLattice | (intros; apply GlobalTheory.HtGen.PointDet.pairDet_htLattice <;> assumption)
end
