import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlowOrbitFirstMinimumOfIsotropicFlowMajorant
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModerateGrowthOfFirstMinimumAndFlowBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedIsSecZeroKeySection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TensorObjectAndCurveExistsIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmLettersIsLieBasisAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeBaseChangeLocalRingsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountAsmPfB

section
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

namespace GlobalTheory.CuspFrom.FlowMaj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma majForm_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ w u = conj (X.Hf x τ u w) := by
  rw [X.Hf_eq_jp, X.Hf_eq_jp, hermC_conj τ.1 X.Gm_herm, X.hermC_jp_left hx]

lemma majForm_sub_smul (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v e w : Fin r → ℂ) :
    X.Hf x τ (v - a • e) w = X.Hf x τ v w - a * X.Hf x τ e w := by
  simp only [X.Hf_eq_jp, X.jp_sub, X.jp_smul, hermC_sub_left, hermC_smul_left]

lemma maj_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  have h := X.Hf_self hx τ 0
  rw [X.Hf_eq_jp, hermC_zero_right] at h
  exact_mod_cast h.symm

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X hx]
  · exact (X.maj_pos hx τ hv).le

lemma maj_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : ℂ) (e u : Fin r → ℂ)
    (h : X.Hf x τ u e = 0) : X.maj x τ (u + a • e) = X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e := by
  have h' : X.Hf x τ e u = 0 := by rw [majForm_conj X hx, h, map_zero]
  have h1 := X.Hf_self hx τ (u + a • e)
  have h2 := X.Hf_self hx τ u
  have h3 := X.Hf_self hx τ e
  simp only [X.Hf_eq_jp] at h h' h1 h2 h3
  simp only [X.jp_add, X.jp_smul, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right,
    h, h', h2, h3] at h1
  have h4 : a * conj a = ((‖a‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a
  have h5 : ((X.maj x τ (u + a • e) : ℝ) : ℂ) = ((X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    linear_combination (X.maj x τ e : ℂ) * h4
  exact_mod_cast h5

lemma majForm_perp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) {e : Fin r → ℂ} (he : e ≠ 0) :
    X.Hf x τ (v - (X.Hf x τ v e / X.Hf x τ e e) • e) e = 0 := by
  have h0 : X.Hf x τ e e ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ he).ne'
  rw [majForm_sub_smul, div_mul_cancel₀ _ h0, sub_self]

lemma majForm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  by_cases hw : w = 0
  · rw [hw, maj_zero X hx, X.Hf_eq_jp, hermC_zero_right]
    simp
  have hp := X.maj_pos hx τ hw
  have h1 := maj_split X hx τ (X.Hf x τ v w / X.Hf x τ w w) w _ (majForm_perp X hx τ v hw)
  rw [sub_add_cancel] at h1
  have h2 := maj_nonneg X hx τ (v - (X.Hf x τ v w / X.Hf x τ w w) • w)
  have h3 : ‖X.Hf x τ v w / X.Hf x τ w w‖ ^ 2 * X.maj x τ w * X.maj x τ w = ‖X.Hf x τ v w‖ ^ 2 := by
    rw [norm_div, X.Hf_self hx τ w, Complex.norm_real, Real.norm_of_nonneg hp.le]
    field_simp
  rw [← h3]
  exact mul_le_mul_of_nonneg_right (by linarith) hp.le

lemma maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  have h1 := X.Hf_self hx τ (X.jp x τ v)
  have h2 := X.Hf_self hx τ v
  rw [X.Hf_eq_jp, X.hermC_jp_jp hx, ← X.Hf_eq_jp, h2] at h1
  exact_mod_cast h1.symm

lemma herm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  have h := majForm_cs X hx τ (X.jp x τ v) w
  rwa [X.Hf_eq_jp, X.jp_jp hx, maj_jp X hx] at h

lemma maj_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hxs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) :
    X.maj (X.flow ξ s x) τ v = X.maj x τ v +
      ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
        (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ)) := by
  have hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [← emb_herm, hξ.2.1, map_zero]
  have he : Data.emb τ.1 ξ ≠ 0 := emb_ne_zero τ.1 hξ.2.2
  have hH := majForm_perp X hx τ v he
  set a := X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with ha
  set u := v - a • Data.emb τ.1 ξ with hu
  have hu0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := by
    rw [hu, hermC_sub_left, hermC_smul_left, hv, hiso, mul_zero, sub_zero]
  have hp : hermC τ.1 X.Gm (X.ppos x τ u) (Data.emb τ.1 ξ) = 0 := by
    have h := hH
    rw [X.Hf_eq_two_ppos, hu0, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  have hpp := Data.ppos_flow X ξ τ hx s hxs u hu0 hp
  have hHy : ∀ w, X.Hf (X.flow ξ s x) τ u w = X.Hf x τ u w := fun w => by
    rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hpp]
  have hm : X.maj (X.flow ξ s x) τ u = X.maj x τ u := by
    have h := hHy u
    rw [X.Hf_self hxs, X.Hf_self hx] at h
    exact_mod_cast h
  have h1 := maj_split X hx τ a _ u hH
  have h2 := maj_split X hxs τ a _ u ((hHy _).trans hH)
  rw [hu, sub_add_cancel, ← hu] at h1 h2
  rw [h1, h2, hm]
  ring

end GlobalTheory.CuspFrom.FlowMaj

namespace GlobalTheory.CuspFrom

theorem flowMajSt_holds : FlowMajSt := fun _ _ _ _ _ X =>
  ⟨fun _ hξ _ hx s hxs τ v hv => FlowMaj.maj_flow X hξ hx s hxs τ v hv,
    fun _ hx τ v w => ⟨FlowMaj.herm_cs X hx τ v w, FlowMaj.majForm_cs X hx τ v w⟩⟩

end GlobalTheory.CuspFrom
end

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz : FlowMajSt := by
  atlas_forward_decl GlobalTheory.CuspFrom.flowMajSt_holds
end

section
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.Koecher

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains in

theorem fj_le_slice (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (ξ : Fin r → E) (hξ : X.IsIso ξ)
    (ν : X.Ψ → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) (y : X.Ψ → ℝ) (M : ℝ)
    (hy : ∀ τ, 0 < X.tt ξ x τ + y τ)
    (hM : ∀ u : X.Ψ → ℝ, ‖P (X.flow ξ (fun τ => (u τ : ℂ) + (y τ : ℂ) * Complex.I) x)‖ ≤ M) :
    ‖X.fj la ξ ν P x‖ * Real.exp (-4 * Real.pi * ∑ τ, ν τ * y τ) ≤ M := by
  classical
  obtain ⟨bs, hω⟩ := FlowMeanContinuity.exists_basis X la
  have hωp : ∀ j, bs j ∈ X.periods la := by
    intro j
    have : bs j ∈ Submodule.span ℤ (Set.range bs) := Submodule.subset_span ⟨j, rfl⟩
    rw [hω] at this
    exact this
  have hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, bs.repr v j * bs j τ = v τ := by
    intro v τ
    conv_rhs => rw [← bs.sum_repr v]
    simp [Finset.sum_apply, mul_comm]
  by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * bs j τ = k
  swap
  · have h0 : X.fj la ξ ν P x = 0 := by
      unfold Data.fj
      rw [if_neg]
      intro hall
      exact hf fun j => hall _ (hωp j)
    rw [h0, norm_zero, zero_mul]
    exact (norm_nonneg _).trans (hM 0)
  choose k hk using hf
  rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx bs hω ν k hk]
  change ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x bs) 0 k‖ * _ ≤ _
  have hm : ∀ τ, 0 < X.maj x τ (Data.emb τ.1 ξ) :=
    fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
  have hc := c_pos X
  set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => bs.repr y j with hb'
  have hb'ω : ∀ τ, ∑ j, b' j * bs j τ = y τ := hrepr y
  have hb'Ω : b' ∈ FractionalSliceDomains.Om X ξ x bs := by
    show (fun τ => ∑ j, b' j * bs j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
    rw [mem_admissibleImaginary_iff X hx hξ]
    intro τ
    rw [hb'ω]
    have h1 := mul_pos (hc τ) (hm τ)
    have h2 := mul_pos (hy τ) h1
    have e : (X.tt ξ x τ + y τ) * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        1 + X.c τ * y τ * X.maj x τ (Data.emb τ.1 ξ) := by
      rw [Data.tt, add_mul, one_div_mul_cancel h1.ne']
      ring
    rwa [e] at h2
  have hind := ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (FractionalSliceDomains.Om X ξ x bs) (hfun X P ξ x bs)
    (Om_open_conn X bs hx).1 (Om_open_conn X bs hx).2 (hfun_diff X bs P la hP hx hξ)
    (hfun_periodic X bs P la hP hx hξ hω) 0 (zero_mem_Om X bs hx hξ) b' hb'Ω k
  rw [hind]
  have hslice : ∀ t : Fin (Fintype.card X.Ψ) → ℝ,
      ‖hfun X P ξ x bs (fun k => (t k : ℂ) + (b' k : ℂ) * Complex.I)‖ ≤ M := by
    intro t
    have h := hM (fun τ => ∑ j, t j * bs j τ)
    unfold hfun
    convert h using 4
    funext τ
    rw [← hb'ω τ]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hbd := ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x bs) b' k _ hslice
  have hsum : ∑ j, (k j : ℝ) * b' j = 2 * ∑ τ, ν τ * ∑ j, b' j * bs j τ := by
    simp only [← hk, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum] at hbd
  simp only [hb'ω] at hbd
  convert hbd using 3
  ring

theorem exists_ne (h : 1 < Module.finrank ℚ E / 2) (τ₀ : X.Ψ) : ∃ τ₁ : X.Ψ, τ₁ ≠ τ₀ := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset (E →+* ℂ)) ⊆ {τ₀.1, ComplexEmbedding.conjugate τ₀.1} := by
    intro τ _
    by_cases hτ : τ ∈ X.Ψ
    · have := congrArg Subtype.val (hne ⟨τ, hτ⟩)
      simp only at this
      simp [this]
    · have h2 : ComplexEmbedding.conjugate τ ∈ X.Ψ := by
        by_contra h3
        exact hτ ((X.cmType τ).mpr h3)
      have := congrArg Subtype.val (hne ⟨_, h2⟩)
      simp only at this
      have h4 : τ = ComplexEmbedding.conjugate τ₀.1 := by
        rw [← this]
        exact (star_star τ).symm
      simp [h4]
  have h1 := (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, NumberField.Embeddings.card] at h1
  omega

theorem eq_zero_of_exp_le {a b c K A : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : ∀ L : ℝ, 1 ≤ L → a * Real.exp (b * L - c) ≤ K * L ^ A) : a = 0 := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A b hb).const_mul (K * Real.exp c)
  rw [mul_zero] at ht
  refine le_antisymm (ge_of_tendsto ht ?_) ha
  filter_upwards [eventually_ge_atTop 1] with L hL
  have h1 := mul_le_mul_of_nonneg_right (h L hL) (Real.exp_pos (c - b * L)).le
  rw [mul_assoc, ← Real.exp_add] at h1
  simp only [sub_add_sub_cancel', sub_self, Real.exp_zero, mul_one] at h1
  refine h1.trans (le_of_eq ?_)
  rw [sub_eq_add_neg, Real.exp_add, neg_mul]
  ring

end GlobalTheory.Koecher

namespace GlobalTheory

open Koecher FjCauchy in

theorem freqNonneg_of_thickBdd : OrbitThickSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), 1 < Module.finrank ℚ E / 2 → X.IsSec la P →
    ThickBdd X (X.pnorm la P) → FreqNonneg X la P := by
  intro hO E _ _ _ r X la P hE hP hT ξ hξ ν x hx hne τ₀
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨τ₁, h10⟩ := exists_ne X hE τ₀
  obtain ⟨ε, hε, hth⟩ := hO E r X ξ hξ x hx
  obtain ⟨S, hS⟩ := hT ε hε
  have ht := tt_pos X hξ hx
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  apply hne
  rw [← norm_eq_zero]
  refine eq_zero_of_exp_le (b := 4 * Real.pi * (-ν τ₀ * X.tt ξ x τ₀))
    (c := 4 * Real.pi * (-ν τ₀ * X.tt ξ x τ₀ + |ν τ₁| * X.tt ξ x τ₁)) (K := |S| / X.nfac la x)
    (A := ∑ τ, |X.spread la τ / 2|) (norm_nonneg _)
    (mul_pos (by positivity) (mul_pos (by linarith) (ht _))) fun L hL => ?_
  have hL0 : 0 < L := by linarith
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  let q : X.Ψ → ℝ := fun τ => (if τ = τ₀ then L else 1) * (if τ = τ₁ then L⁻¹ else 1)
  have hq0 : ∀ τ, 0 < q τ := fun τ => by
    simp only [q]
    split_ifs <;> positivity
  have hqm : ∀ τ, max (q τ) (q τ)⁻¹ ≤ L := fun τ => by
    simp only [q]
    split_ifs with h1 h2 h2
    · exact absurd (h2.symm.trans h1) h10
    · simp [hLi.trans hL]
    · simp [hLi.trans hL]
    · simp [hL]
  have hq1 : ∀ τ, 1 ≤ max (q τ) (q τ)⁻¹ := fun τ => by
    rcases le_total 1 (q τ) with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_le_inv₀ (hq0 τ)).mpr h)
  have hqp : ∏ τ, q τ = 1 := by
    simp only [q, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hL0.ne'
  let y : X.Ψ → ℝ := fun τ => (q τ - 1) * X.tt ξ x τ
  have hty : ∀ τ, X.tt ξ x τ + y τ = q τ * X.tt ξ x τ := fun τ => by simp only [y]; ring
  have hy : ∀ τ, 0 < X.tt ξ x τ + y τ := fun τ => by rw [hty]; exact mul_pos (hq0 τ) (ht τ)
  refine le_trans ?_ (fj_le_slice X la P hP ξ hξ ν x hx y _ hy fun u => ?_)
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have e : ∑ τ, ν τ * y τ = ν τ₀ * ((L - 1) * X.tt ξ x τ₀) + ν τ₁ * ((L⁻¹ - 1) * X.tt ξ x τ₁) := by
      rw [Fintype.sum_eq_add τ₀ τ₁ h10.symm]
      · simp [y, q, h10, h10.symm]
      · rintro τ ⟨h1, h2⟩
        simp [y, q, h1, h2]
    rw [e]
    have h1 : ν τ₁ * ((L⁻¹ - 1) * X.tt ξ x τ₁) ≤ |ν τ₁| * X.tt ξ x τ₁ := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (ht τ₁)]
      refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (ht τ₁).le ?_) (abs_nonneg _)
      have := inv_pos.mpr hL0
      rw [abs_le]
      constructor <;> linarith
    nlinarith [Real.pi_pos]
  · set s : X.Ψ → ℂ := fun τ => (u τ : ℂ) + (y τ : ℂ) * I with hs
    have him : ∀ τ, (s τ).im = y τ := fun τ => by simp [hs]
    have hd : X.flow ξ s x ∈ X.dom := flow_mem_dom X hξ hx s fun τ => by rw [him]; exact hy τ
    have hprod : ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ := by
      simp only [tt_flow X hξ hx s hd, him, hty]
      rw [Finset.prod_mul_distrib, hqp, one_mul]
    have hb : ‖P (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x) ≤ S := hS _ hd (hth s hd hprod)
    have hn' := FlowCoefficientBounds.nfac_pos X hd la
    have hN : X.nfac la x / X.nfac la (X.flow ξ s x) ≤
        ∏ τ, max (1 + (s τ).im / X.tt ξ x τ) (1 + (s τ).im / X.tt ξ x τ)⁻¹ ^ (X.spread la τ / 2) :=
      (m3bNorm_holds r X _ (isIsoV_embV X hξ) la x hx s hd).2
    have hqe : ∀ τ, 1 + (s τ).im / X.tt ξ x τ = q τ := fun τ => by
      rw [him]
      simp only [y]
      rw [mul_div_cancel_right₀ _ (ht τ).ne']
      ring
    simp only [hqe] at hN
    have hN2 : ∏ τ, max (q τ) (q τ)⁻¹ ^ (X.spread la τ / 2) ≤ L ^ ∑ τ, |X.spread la τ / 2| := by
      rw [Real.rpow_sum_of_pos hL0]
      refine Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (zero_le_one.trans (hq1 τ)) _) fun τ _ => ?_
      exact (Real.rpow_le_rpow_of_exponent_le (hq1 τ) (le_abs_self _)).trans
        (Real.rpow_le_rpow (zero_le_one.trans (hq1 τ)) (hqm τ) (abs_nonneg _))
    calc ‖P (X.flow ξ s x)‖ ≤ |S| / X.nfac la (X.flow ξ s x) := by
          rw [le_div_iff₀ hn']
          exact hb.trans (le_abs_self S)
      _ = |S| / X.nfac la x * (X.nfac la x / X.nfac la (X.flow ξ s x)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hN.trans hN2) (by positivity)

end GlobalTheory
end

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.koecher_principle_flagDomain_frequencies_nonneg : OrbitThickSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), 1 < Module.finrank ℚ E / 2 → X.IsSec la P → ThickBdd X (X.pnorm la P) → FreqNonneg X la P := by
  atlas_forward_decl GlobalTheory.freqNonneg_of_thickBdd
end

section
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

namespace GlobalTheory.CuspStep

theorem half_plane_bound {g : ℂ → ℂ} {M C : ℝ} (hd : DifferentiableOn ℂ g {z | 0 ≤ z.re})
    (hM : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ M) (hC : ∀ y : ℝ, ‖g (y * I)‖ ≤ C) : ‖g 1‖ ≤ C := by
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) ?_ ⟨0, by norm_num, 0, ?_⟩ ?_ hC (by simp)
  · refine DifferentiableOn.diffContOnCl ?_
    rw [Complex.closure_setOf_lt_re]
    exact hd
  · refine Asymptotics.IsBigO.of_bound M ?_
    refine Filter.Eventually.filter_mono inf_le_right ?_
    rw [Filter.eventually_principal]
    intro z hz
    simpa using hM z (le_of_lt hz)
  · refine ⟨M, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
    exact hM y (by simpa using hy)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem differentiable_flow (ξ : Fin r → E) (a : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun z : ℂ => X.flow ξ (fun τ => z * a τ) x) := by
  refine differentiable_pi.mpr fun τ => differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => ?_
  simp only [Data.flow, Data.flowMat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem nfac_flow_real (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hs : ∀ τ, (s τ).im = 0) : X.nfac la (X.flow ξ s x) = X.nfac la x := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => by rw [hs, add_zero]; exact FjCauchy.tt_pos X hξ hx τ
  have h := m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx s hd
  simp only [hs, zero_div, add_zero, inv_one, min_self, max_self, Real.one_rpow, Finset.prod_const_one] at h
  have h1 : X.nfac la x / X.nfac la (X.flow ξ s x) = 1 := le_antisymm h.2 h.1
  have hn := FlowCoefficientBounds.nfac_pos X hd la
  rw [div_eq_one_iff_eq hn.ne'] at h1
  exact h1.symm

theorem norm_flow_le {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    ‖P (X.flow ξ s x)‖ ≤ ∑' ν : X.Ψ → ℝ, ‖X.fj la ξ ν P x‖ := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx τ) (hs τ)
  have h0 := m3bExp_holds r X la P hP ξ hξ x hx 0 (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
  have hsum : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr h0.summable
  have h1 := m3bExp_holds r X la P hP ξ hξ x hx s hd
  refine h1.norm_le_of_bounded hsum.hasSum fun ν => ?_
  by_cases hz : X.fj la ξ ν P x = 0
  · simp [hz]
  · have hν := hF ξ hξ ν x hx hz
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hsn : 0 ≤ ∑ τ, ν τ * (s τ).im := Finset.sum_nonneg fun τ _ => mul_nonneg (hν τ) (hs τ)
    have : (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ).re = -(4 * Real.pi * ∑ τ, ν τ * (s τ).im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]
    rw [this]
    have := Real.pi_pos
    have : 0 ≤ 4 * Real.pi * ∑ τ, ν τ * (s τ).im := by positivity
    linarith

theorem stepBound (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (w : ℝ) (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    (hw : ∀ τ, X.spread la τ / 2 ≤ w) : StepBound X w (X.pnorm la P) := by
  intro ξ hξ x hx q hq B hB
  have ht := FjCauchy.tt_pos X hξ hx
  set b : X.Ψ → ℂ := fun τ => I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ) with hb
  have hbim : ∀ τ, (b τ).im = (q τ - 1) * X.tt ξ x τ := fun τ => by
    simp only [hb, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbre : ∀ τ, (b τ).re = 0 := fun τ => by
    simp only [hb, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbn : ∀ τ, (b τ).im ≤ 0 := fun τ => by
    rw [hbim]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hq τ).2]) (ht τ).le
  have hx' : X.flow ξ b x ∈ X.dom := FjCauchy.flow_mem_dom X hξ hx b fun τ => by
    rw [hbim]; nlinarith [mul_pos (hq τ).1 (ht τ)]
  set x' := X.flow ξ b x with hx'def
  have hn' := FlowCoefficientBounds.nfac_pos X hx' la
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have him : ∀ z : ℂ, 0 ≤ z.re → ∀ τ, 0 ≤ (z * -b τ).im := fun z hz τ => by
    simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, hbre, neg_zero, mul_zero, add_zero]
    exact mul_nonneg hz (by linarith [hbn τ])
  have hreal : ∀ y : ℝ, ‖P (X.flow ξ (fun τ => (y * I) * -b τ) x')‖ ≤ B / X.nfac la x' := fun y => by
    have hs : ∀ τ, ((y * I : ℂ) * -b τ).im = 0 := fun τ => by simp [hbre]
    rw [le_div_iff₀ hn', ← nfac_flow_real X la hξ hx' _ hs]
    have h := hB fun τ => ((y * I : ℂ) * -b τ).re
    have he : X.flow ξ (fun τ => (y * I) * -b τ) x' =
        X.flow ξ (fun τ => (((y * I : ℂ) * -b τ).re : ℂ) + b τ) x := by
      rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
      congr 1
      funext τ
      simp only [Pi.add_apply]
      congr 1
      exact Complex.ext (by simp) (by rw [hs]; simp)
    rw [he]
    exact h
  have key := half_plane_bound (g := fun z => P (X.flow ξ (fun τ => z * -b τ) x'))
    (hP.1.comp (differentiable_flow X ξ (fun τ => -b τ) x').differentiableOn fun z hz =>
      FjCauchy.flow_mem_dom X hξ hx' _ fun τ =>
        add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx' τ) (him z hz τ))
    (fun z hz => norm_flow_le X hP hF hξ hx' _ (him z hz)) hreal
  have he : X.flow ξ (fun τ => 1 * -b τ) x' = x := by
    rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
    have : ((fun τ => 1 * -b τ) + b) = 0 := by funext τ; simp
    rw [this, EmbeddingHermitianPairs.flow_zero]
  simp only [he] at key
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans key
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hn'))
  have hr := (m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx b hx').2
  have hr2 : X.nfac la x / X.nfac la x' ≤ ∏ τ, q τ ^ (-w) := by
    refine le_trans hr (Finset.prod_le_prod (fun τ _ => ?_) fun τ _ => ?_)
    all_goals
      have hqq : 1 + (b τ).im / X.ttV (X.embV ξ) x τ = q τ := by
        change 1 + (b τ).im / X.tt ξ x τ = q τ
        rw [hbim, mul_div_assoc, div_self (ht τ).ne']; ring
      have h1 : 1 ≤ (q τ)⁻¹ := (one_le_inv₀ (hq τ).1).mpr (hq τ).2
      simp only [hqq, max_eq_right ((hq τ).2.trans h1)]
    · positivity
    · rw [Real.rpow_neg (hq τ).1.le, ← Real.inv_rpow (hq τ).1.le]
      exact Real.rpow_le_rpow_of_exponent_le h1 (hw τ)
  calc X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
    _ ≤ B / X.nfac la x' * X.nfac la x := mul_le_mul_of_nonneg_right key hn.le
    _ = B * (X.nfac la x / X.nfac la x') := by ring
    _ ≤ B * ∏ τ, q τ ^ (-w) := mul_le_mul_of_nonneg_left hr2 hB0

end GlobalTheory.CuspStep
end

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (w : ℝ), X.IsSec la P → FreqNonneg X la P → (∀ τ, X.spread la τ / 2 ≤ w) → StepBound X w (X.pnorm la P) := by
  atlas_forward_decl GlobalTheory.CuspStep.stepBound
end

section
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.CuspLimit

open Classical in

theorem tendsto_dirichlet {ι : Type*} (A : ι → ℂ) (a : ι → ℝ) (F : ℝ → ℂ) (T : ℝ)
    (ha : ∀ i, A i ≠ 0 → 0 ≤ a i)
    (hs : ∀ t, T < t → HasSum (fun i => A i * (Real.exp (-(a i * t)) : ℂ)) (F t)) :
    Tendsto F atTop (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
  have h0 : Summable fun i => ‖A i * (Real.exp (-(a i * (T + 1))) : ℂ)‖ :=
    (hs (T + 1) (by linarith)).summable.norm
  have hlim : Tendsto (fun t : ℝ => ∑' i, A i * (Real.exp (-(a i * t)) : ℂ)) atTop
      (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence h0 (fun i => ?_) ?_
    · by_cases hi : A i = 0
      · simp [hi]
      by_cases hz : a i = 0
      · simp [hz]
      have hp : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hz)
      rw [if_neg hz]
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(a i * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul (A i)
      simpa using h2
    · filter_upwards [eventually_ge_atTop (T + 1)] with t ht i
      by_cases hi : A i = 0
      · simp [hi]
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      exact neg_le_neg (mul_le_mul_of_nonneg_left ht (ha i hi))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  exact (hs t ht).tsum_eq

theorem fj_zero_eq_zero_of_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  intro E _ _ _ r X la P ξ x s d T g hP hnn hξ hx hd hg hw
  classical
  have hpi := Real.pi_pos
  set F : ℝ → ℂ := fun t => P (X.flow ξ (fun τ => s τ + (I * t) * (d τ : ℂ)) x) with hF
  have him : ∀ t : ℝ, T < t → T < (I * (t : ℂ)).im := fun t ht => by simpa using ht
  have h1 := tendsto_dirichlet g (fun m : ℤ => 2 * Real.pi * m) F T
    (fun m hm => by
      have : 0 < m := by
        by_contra h
        exact hm (hg m (not_lt.mp h))
      positivity)
    (fun t ht => by
      have h := (hw _ (him t ht)).2
      convert h using 3 with m
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi, ← Complex.exp_int_mul]
      push_cast
      congr 1
      linear_combination (-(2 * (Real.pi : ℂ) * m * t)) * Complex.I_mul_I)
  have e1 : (∑' m : ℤ, if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = 0 := by
    have : (fun m : ℤ => if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = fun _ => 0 := by
      funext m
      split_ifs with h
      · have hm : m = 0 := by simpa [hpi.ne'] using h
        exact hg m hm.le
      · rfl
    rw [this, tsum_zero]
  have h2 := tendsto_dirichlet
    (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
    (fun ν => 4 * Real.pi * ∑ τ, ν τ * d τ) F T
    (fun ν hν => by
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hν)
      have : 0 ≤ ∑ τ, ν τ * d τ := Finset.sum_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le
      positivity)
    (fun t ht => by
      have h := m3bExp_holds r X la P hP ξ hξ x hx _ (hw _ (him t ht)).1
      convert h using 2 with ν
      rw [mul_assoc]
      congr 1
      push_cast
      rw [← Complex.exp_add]
      congr 1
      have e : ∑ τ, (ν τ : ℂ) * (s τ + I * t * (d τ : ℂ)) =
          ∑ τ, (ν τ : ℂ) * s τ + I * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by ring
      rw [e]
      linear_combination (-(4 * (Real.pi : ℂ) * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ))) * Complex.I_mul_I)
  rw [tsum_eq_single (0 : X.Ψ → ℝ) (fun ν hν => by
    split_ifs with h
    · by_contra hne
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hne)
      have hz : ∑ τ, ν τ * d τ = 0 := by simpa [hpi.ne'] using h
      refine hν (funext fun τ => ?_)
      have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le).mp hz τ
        (Finset.mem_univ τ)
      exact (mul_eq_zero.mp this).resolve_right (hd τ).ne'
    · rfl)] at h2
  rw [e1] at h1
  simpa using tendsto_nhds_unique h2 h1

end GlobalTheory.CuspLimit
end

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  atlas_forward_decl GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.CuspFrom.PeriodTriple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}

theorem exists_isExp_of_sabMap {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} (B : GlobalTheory.CM.PAT H (Sp ℂ))
    (m : SABMap B.t t y) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (hP : IsPeriod D ty P)
    (hol : IsHolTo Set.univ fun z => (e z).left) (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e)
    (ker : ∀ z, e z = 1 ↔ z ∈ P.range) (lin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    ∃ ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G), GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) y hy
  have hp' : ∀ z, (p.symm (e z)).left ≫ m.φ = (e z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => p.symm (e z), hP, ?_, fun z w => ?_, p.symm.surjective.comp onto, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · refine ThetaPoint.isHolTo_fibre m.cart.1 _ (fun z => (Over.w (p.symm (e z))).trans hid) ?_
    have h : (fun z => (p.symm (e z)).left ≫ m.cm.F) = fun z => (e z).left := funext hp'
    exact h ▸ hol
  · beta_reduce
    rw [add, map_mul]
  · exact (map_eq_one_iff _ p.symm.injective).trans (ker z)
  · beta_reduce
    rw [lin, p.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
    exact congrArg (· ≫ _) (hp' z).symm
  · exact (GlobalTheory.CM.ExCompare.weilIs_iff m _ _ hy k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (weil k a b c hk hc)

theorem exists_isExp_of_rank_zero (l : Level H) (hD : D.p + D.q = 0) (hP : IsPeriod D ty P) :
    ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)),
      GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  obtain ⟨B, hB, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H D l _ _ _ _
    (Models.RankZero.zeroObj hD l (spMap (algebraMap (KA l) ℂ)))
  have hz : IsIso B.t.G.hom := by
    rw [hB]
    exact Models.RankZero.isIso_zeroTriple _
  have := Models.RankZero.subsingleton_La hD
  have h0 : ∀ z : Fin g → ℂ, z = 0 := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1 ▸ Submodule.mem_top
    refine (Submodule.span_le (p := ⊥)).2 ?_ hz
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a 0, map_zero]
    exact Submodule.zero_mem _
  refine ⟨B, fun _ => 1, hP, fun U f => ⟨?_, differentiableOn_const _⟩, fun _ _ => (_root_.mul_one _).symm,
    fun x => ⟨0, Models.RankZero.hom_unique hz _ _⟩, fun z => ⟨fun _ => ⟨0, by rw [map_zero, h0 z]⟩, fun _ => rfl⟩,
    fun _ _ => Models.RankZero.hom_unique hz _ _, fun k a b c hk hc => ?_⟩
  · simp only [Set.mem_univ, true_and]
    exact isOpen_const
  · have e : c = 1 := Units.ext (by rw [hc, Subsingleton.elim b 0, map_zero]; simp)
    rw [e, unitOn, map_one]
    exact Models.RankZero.weilIs_zero hz B.t.PP.isLB (Models.RankZero.triv_rig hz _) _ _ _

end GlobalTheory.CuspFrom.PeriodTriple

namespace GlobalTheory.CuspFrom

theorem exists_pat_isExp_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  intro E _ _ _ H l₀ DB g ty PB hty hP
  rcases Nat.eq_zero_or_pos (DB.p + DB.q) with h0 | hpq
  · exact PeriodTriple.exists_isExp_of_rank_zero l₀ h0 hP
  have kn := known_holds
  obtain ⟨l, hA⟩ : ∃ l : Level H, l.A = 1 := ⟨{ l₀ with A := 1, A_pos := one_pos }, rfl⟩
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, -, -, ⟨add, onto, hol, -⟩, ker, lin, weil, -⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws
    E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty DB LinearMap.id PB
    ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨U, hU, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H DB l _ _ _ _ Xo.univ
  obtain ⟨B, m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ y U
  exact ⟨B, PeriodTriple.exists_isExp_of_sabMap B (hU ▸ m) e hP hol add onto ker lin weil⟩

end GlobalTheory.CuspFrom
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalCMTriple_exponential_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  atlas_forward_decl GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.CuspFrom

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_similar_zeta
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a)) ∧
      ∀ n : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν n := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf, fun n hn => ?_⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]
  · rw [zpow_natCast]
    exact hν n hn

end

theorem familyUnif_lattice_similar_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty)
    (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧
      (∀ a, ∃ e, f l.A a = U.t i a + l.A • e) ∧
      σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) := by
  obtain ⟨-, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, -, -, h5, h6, h7⟩ := tateIso_similar_zeta
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h5, fun a ha => ?_, fun a => ?_, ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a
  · rw [← hζ, h7 _ l.A_pos]
    exact expNegUnit_zpow_val _ _

theorem exists_arcIn_input : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x B hσ _
  let _ := H.starRing
  intro A gam ξ DB tyB eB ex ⟨hgam, _, T₀, hT₀⟩ hrk hbe ⟨hχ, hψ⟩ ⟨hF, hty, _, hEF, _⟩ hp hq hp1 hq1
    ⟨_, hol, add, onto, ker, lin, weil⟩
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨T, m, hg⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (RingHom.id ℂ)) B
  obtain ⟨-, hiso⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ _ B _ m
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ T.t.PP).1 T.t.sym
  have := T.t.act.hom H.w0
  obtain ⟨w, hw, hw'⟩ := CxFibre.exists_primGen T.t.PP (T.t.act.act H.w0) T.t.prim
  let oa : T.pol.OAct (𝓞 E) := ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hK.laws.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩
  obtain ⟨u, χ, hgP, lam, hAH, hrig, hθ, hex⟩ := CxFibre.exists_holUnif_of_exp hK.theta B.t.PP.isLB
    (spMap (RingHom.id ℂ)) T.pol T.t.PP.rig
    T.t.PP.rigGen m.φ m.cart ⟨w₀, hw₀⟩ A.abelian₂ A.discrete A.full A.Hm A.Hm_herm A.Hm_pos (fun a b => A.Ef a b) A.Ef_eq
    ex hol add onto
    (fun z => (ker z).trans ⟨fun ⟨a, ha⟩ => ha ▸ (eB a).2, fun hz => ⟨eB.symm ⟨z, hz⟩, by simp⟩⟩)
    (fun n a b c hn hc => by
      obtain ⟨a, rfl⟩ := eB.surjective a
      obtain ⟨b, rfl⟩ := eB.surjective b
      exact weil n a b c hn (by rw [hEF]; exact hc))
  have hact : ∀ (a : 𝓞 E) z, u.ex (fun i => tyB i (a : E) * z i) = u.ex z ≫ T.t.act.act a := fun a z =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by
      rw [hex, lin, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hex])
      (by rw [Over.w, Over.w]))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (A.F a z) = u.ex z ≫ T.t.act.act a := fun a z => by
    rw [← hact]; exact congrArg u.ex (funext (hF a z))
  obtain rfl : χ = fun b : u.Λ => A.chi ⟨b, lam.le b.2⟩ := funext fun a => by
    rw [CxFibre.chi_eq T.t.PP.isLB _ w hw u A.Hm χ hAH (A.F H.w0) (hact' _) a
      ⟨_, lam.ge (A.F_mem H.w0 a (lam.le a.2))⟩ rfl, hχ]
    have h₁ := A.Ef_eq_im (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩
    rw [← A.H_conj, Complex.conj_im] at h₁
    have h₂ : (hermForm A.Hm a (A.F H.w0 a)).im = -(A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ : ℤ) := by
      rw [h₁, neg_neg]; rfl
    generalize A.Ef (A.FLam H.w0 ⟨a, lam.le a.2⟩) ⟨a, lam.le a.2⟩ = n at h₂
    rw [h₂, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  obtain ⟨s, hs, -⟩ := hT₀ ((T₀ + 1 : ℝ) * Complex.I) (by simp)
  obtain ⟨f, ν, f₁, f₂, f₃, f₄, f₅, f₆⟩ :=
    familyUnif_lattice_similar_zeta E H Dw l Xo _ _ _ Uw.F (Uw.ik k) _ (Uw.period k ⟨_, hs⟩)
  obtain ⟨a, Λ, hA, -, -, -, -, -, -, heta, hetaA⟩ := GlobalTheory.ArcOfModel.exists_arcIn hK.laws hK.laws2 Dw l
    (RingHom.id c.F) σ T.pol T.t.PP.rig T.t.PP.rigGen T.t.cub sym hsym hsym' oa ⟨w, hw, hw'⟩ A u lam hAH hrig
    (fun j _ => hθ j) hact' hψ (Module.nontrivial_of_finrank_pos (R := 𝓞 E) (hrk ▸ one_pos)) hbe _ gam hgam
    (Uw.F.t (Uw.ik k)) f ν f₁ (fun n hn v => ((f₂ n hn).1 v).1) (fun n hn => (f₂ n hn).2)
    f₃ f₄ f₅
    (fun z hz => (congrArg σ (Subtype.ext hz)).trans f₆)
    (fun ρ hρ τ => by
      obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
      have hρ' : σ ρ = H.rt0 := by
        rw [← hσ]
        exact congrArg σ (Subtype.ext hρ)
      refine ⟨_, CxFibre.lieMult_card hK.theta T.pol hgP u _ tyB hact τ₀, ?_⟩
      rw [hrk, hρ']
      split_ifs with h
      · rw [(hty τ₀).1 h]; omega
      · rw [(hty τ₀).2 h]; omega)
  refine ⟨a, Λ.toGtAn₀, hA, fun v q hq => ?_, fun v q hq => ?_⟩
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (heta v)]
    exact qk_equiv_refl a.bimult _
  · rw [(TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) (RingHom.comp_id _) _).unique hq (hetaA v)]
    exact qk_equiv_refl a.bimult _

end GlobalTheory.CuspFrom
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (B : GlobalTheory.CM.PAT H (Sp ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (hA : Λ.A = A), (∀ v, Λ.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v)))) ∧ ∀ v, Λ.Lifts (aC.etaA v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  atlas_forward_decl GlobalTheory.CuspFrom.exists_arcIn_input
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem linearIndependent_symm_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : T) :
    LinearIndependent ℂ (fun i : Fin (m τ) => L.symm (Pi.single (e.symm ⟨τ, i⟩) 1)) := by
  have hinj : Function.Injective fun i : Fin (m τ) => e.symm ⟨τ, i⟩ :=
    e.symm.injective.comp sigma_mk_injective
  have := ((Pi.basisFun ℂ (Fin g)).linearIndependent.comp _ hinj).map' L.symm.toLinearMap L.symm.ker
  have hf : (fun i : Fin (m τ) => L.symm (Pi.single (e.symm ⟨τ, i⟩) 1)) =
      L.symm.toLinearMap ∘ ((Pi.basisFun ℂ (Fin g)) ∘ fun i : Fin (m τ) => e.symm ⟨τ, i⟩) := by
    funext i
    simp
  rw [hf]
  exact this

theorem point_exp_eq_of_isometry_levels (hK : Known) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La)
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hpq : 1 ≤ D.p + D.q) (hσ : σ (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H D.p D.q ty) (hA' : ∀ a, ∃ x, gm (Fu.t i a) = Fu.t i' a + l.A • x)
    (hP : IsPeriod (Fu.Di i) ty P) (hP' : IsPeriod (Fu.Di i') ty P')
    (hiso : ∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e)
    (hL : ∀ u, P' (gm u) = L (P u)) : Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  have hu : Fu.u i P = Fu.u i' P' :=
    (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hσ hty (Fu.Di i) (Fu.Di i')
      (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.ex_diff i P hP).1, (Fu.ex_diff i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', GlobalTheory.ArcCM.isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.ex_diff i' P' hP').1, (Fu.ex_diff i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP',
        Fu.ex_weil i' P' hP', Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ⟨gm, L, hiso, hM, hA', hL⟩
  obtain rfl : i = i' := Fu.disj i i' P P' hP hP' hu
  letI : StarRing (𝓞 E) := H.starRing
  exact GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hM hA' hL

theorem flowTie_of_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hY hLM hLA O _ β Y χ W Ha
  have hK : Known := GlobalTheory.ArcCM.known_holds
  let := H.starRing
  let Λ' : GtAn₀ (aC.restrict β) := ⟨Λ.toGtDict, Λ.be_eq⟩
  obtain ⟨g₁, h₁, e1, e2, e3, e4⟩ :=
    GlobalTheory.ArcCompare.holArc_agrees hK E H Dw l Xo c σ O β Y (aC.restrict β) χ W Uw.g _ Uw.F Ha Λ'
  obtain ⟨o1, ⟨t', o2, o3⟩, T₀, o4⟩ := hO
  have hw : max Ha.T T₀ < (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I) = w₁ at hw
  obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
  obtain ⟨s₁, hs₁, h, hh⟩ := o4 w₁ hw2
  let gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La := g₁.trans gam.symm
  let L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ) := h₁.trans h.symm
  have hgm : ∀ u, gam (gm u) = g₁ u := fun u => gam.apply_symm_apply _
  have hg1 : ∀ v, g₁ (gm.symm v) = gam v := fun v => by rw [← hgm, gm.apply_symm_apply]
  have hEF : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gm u) (gm v) = (Uw.F.Di Ha.i).EF u v := fun u v => by
    rw [← o1, hgm, hgm]; exact e4 u v
  have hEF' : ∀ u v, (Uw.F.Di (Uw.ik k)).EF u v = (Uw.F.Di Ha.i).EF (gm.symm u) (gm.symm v) := fun u v => by
    rw [← hEF, gm.apply_symm_apply, gm.apply_symm_apply]
  have hP : ∀ u, Uw.Pm k ⟨_, hs₁⟩ (gm u) = L (Ha.Pw w₁ u) := fun u => by
    apply h.injective
    rw [hh, hgm]
    exact (e3 w₁ u).symm.trans (h.apply_symm_apply _).symm
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (Subsingleton.elim _ _) hξ.2.2
    · exact hr
  have hpq : 1 ≤ Dw.p + Dw.q := by
    rw [← hU.1]
    exact hr
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e
  have h0 : ∀ v, h₁ (Ha.P₀ (Uw.F.t Ha.i v)) = Λ.A.P0 (g₁ (Uw.F.t Ha.i v)) := fun v => by
    have := e3 0 (Uw.F.t Ha.i v)
    rw [Ha.Pw_eq, zero_smul, add_zero] at this
    exact this.trans (by rw [AnArc.Pw_apply, zero_smul, add_zero])
  have hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.M • e := by
    intro v hv
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelM v hv
    have hq : q = Λ.toGtDict.qk l.M (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.eta v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.eta v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hLM v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add, map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  have hlevA : ∀ v, ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.A • e := by
    intro v
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelA v
    have hq : q = Λ.toGtDict.qk l.A (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.etaA v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.etaA v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hLA v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add, map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  obtain ⟨-, p2⟩ := point_exp_eq_of_isometry_levels hK Uw.F Ha.i (Uw.ik k) (Ha.Pw w₁) (Uw.Pm k ⟨_, hs₁⟩) gm L hpq
    hσ hty hlevA (Ha.period w₁ hw1) (Uw.period k _) hEF hlev hP
  obtain ⟨nn, n1, n2, n3, n4, n5, n6⟩ :=
    GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y (aC.restrict β) χ W _ _ Uw.F Ha
  have hlin : ∀ w w' v, Ha.Pw w v = Ha.Pw w' v + (w - w') • Ha.Pw w' (nn v) := by
    intro w w' v
    rw [Ha.Pw_eq, Ha.Pw_eq, Ha.Pw_eq, n1 (nn v), n4 _ (n3 v), map_zero, smul_zero, add_zero, ← n1, sub_smul]
    abel
  have hyg : ∀ u, Ha.y u = Λ.eX (g₁ u).y := fun u => (e2 u).symm
  let nn' : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La :=
    gm.toLinearMap ∘ₗ nn ∘ₗ gm.symm.toLinearMap
  have hnn'e : ∀ v, gm.symm (nn' v) = nn (gm.symm v) := fun v => gm.symm_apply_apply _
  let y'' : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] Λ.A.X := Λ.A.yLin ∘ₗ gam.toLinearMap
  have hy'' : Function.Surjective y'' := Λ.A.yLin_surjective.comp gam.surjective
  have hnn'' : ∀ v v', -(Uw.F.Di (Uw.ik k)).EF (nn' v) v' = Λ.A.be (y'' v) (y'' v') := by
    intro v v'
    rw [hEF', hnn'e, n2, hyg, hyg, hg1, hg1]
    exact Λ.be_eq _ _
  have hrep'' : ∀ η : Module.Dual ℤ Λ.A.X, ∃ t, ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = η (y'' v) := by
    intro η
    obtain ⟨t, ht, -⟩ := n6 (η.toAddMonoidHom.comp Λ.eX.symm.toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨gm t, fun v => ?_⟩
    rw [hEF', gm.symm_apply_apply, ht, hyg, hg1]
    show η (Λ.eX.symm (Λ.eX _)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hyt : y'' t' = 0 := by
    have hy0 := n5 (gm.symm t') fun v' hv' => by
      have h3 := o3 (gm v')
      have h4 : (g₁ v').y = 0 := (map_eq_zero_iff _ Λ.eX.injective).1 (by rw [← hyg]; exact hv')
      rw [hgm, h4, map_zero] at h3
      rw [← hEF, gm.apply_symm_apply]
      exact neg_eq_zero.1 h3
    rw [hyg, hg1] at hy0
    exact (map_eq_zero_iff _ Λ.eX.injective).1 hy0
  let x₀ : (U.X k).dom := ⟨_, hs₁⟩
  obtain ⟨-, -, -, -, Hm, hHm⟩ := Uw.period k x₀
  have hκ := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x₀ Hm hσ hU hHm).2.1 hr
  obtain ⟨sE, -, hbe, hsp, -, hform⟩ := GlobalTheory.ArcFlow.rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) y'' hY hκ hy''
    Λ.A.be Λ.A.be_symm Λ.A.be_pos nn' hnn'' hrep'' ξ hξ0 t' o3 hyt
  have hform' : ∀ v, (Uw.φ k (nn' v) : Fin r → E) =
      (-(sE * (U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) • ξ' := fun v => by
    rw [hform v, o2]
  have hξ'0 : herm (U.X k).Gm ξ' ξ' = 0 := hξ.2.1
  have hLs : ∀ z, (Uw.F.ex Ha.i (Ha.Pw w₁) (L.symm z)).left = (Uw.F.ex (Uw.ik k) (Uw.Pm k x₀) z).left := fun z => by
    rw [← p2 (L.symm z), L.apply_symm_apply]
  refine ⟨Ha.T, fun τ => s₁ τ - w₁ * (((τ.1 sE).re : ℝ) : ℂ), fun τ => (τ.1 sE).re,
    fun τ i => L.symm (Pi.single (Uw.e.symm ⟨τ, i⟩) 1), fun τ => hsp τ.1, fun τ => ⟨?_, fun i jj hij => ?_⟩,
    fun w hw => ?_⟩
  · exact linearIndependent_symm_single Uw.e L τ
  · refine GlobalTheory.DerivativeDetermination.type_map Uw.e Uw.F (Uw.period k x₀) (Ha.period w₁ hw1) L.symm.toLinearMap hLs τ _
      (fun j hj => ?_) jj hij
    by_cases hjj : j = Uw.e.symm ⟨τ, i⟩
    · subst hjj; simp
    · exact absurd (Pi.single_eq_of_ne hjj _) hj
  · let Pw' : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ) :=
      L.toLinearMap.toAddMonoidHom.comp ((Ha.Pw w).comp gm.symm.toLinearMap.toAddMonoidHom)
    have hg' : ∀ a b, (Uw.F.Di Ha.i).EF (gm.symm a) (gm.symm b) = (Uw.F.Di (Uw.ik k)).EF a b :=
      fun a b => (hEF' a b).symm
    have hPer : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) Pw' := by
      have := GlobalTheory.UnifCompare.isPeriod_move
        (GlobalTheory.ClassUniq.isPeriod_comp_isometry gm.symm hg' (Ha.period w₁ hw1)) (Uw.period k x₀)
        (GlobalTheory.ClassUniq.isPeriod_comp_isometry gm.symm hg' (Ha.period w hw)) (LinearEquiv.refl _ _) L
        (fun _ _ => rfl) (fun a => by
          show Uw.Pm k x₀ a = L (Ha.Pw w₁ (gm.symm a))
          rw [← hP, gm.apply_symm_apply])
      exact this
    have hPx : ∀ v, Pw' v = Uw.Pm k x₀ v + (w - w₁) • Uw.Pm k x₀ (nn' v) := by
      intro v
      have a1 := hP (gm.symm v)
      rw [gm.apply_symm_apply] at a1
      have a2 := hP (nn (gm.symm v))
      show L (Ha.Pw w (gm.symm v)) = _
      rw [hlin w w₁, map_add, map_smul, ← a1, ← a2]
      rfl
    obtain ⟨hxw, hPw'⟩ := GlobalTheory.ArcFlow.flow_period Uw hσ hU k hκ nn' ξ' hξ'0 sE hbe.1 hform' x₀ (w - w₁) Pw' hPer hPx
    have heq : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x₀.1 =
        (U.X k).flow ξ' (fun τ => (s₁ τ - w₁ * (((τ.1 sE).re : ℝ) : ℂ)) + w * (((τ.1 sE).re : ℝ) : ℂ)) x := by
      rw [ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flow_flow (U.X k) hξ'0]
      congr 1
      funext τ
      simp only [Pi.add_apply]
      ring
    obtain ⟨q1, q2⟩ := point_exp_eq_of_isometry_levels hK Uw.F Ha.i (Uw.ik k) (Ha.Pw w) (Uw.Pm k ⟨_, hxw⟩) gm L
      hpq hσ hty hlevA (Ha.period w hw) (Uw.period k _) hEF hlev (fun u => by
        rw [hPw']
        show L (Ha.Pw w (gm.symm (gm u))) = _
        rw [gm.symm_apply_apply])
    refine ⟨heq ▸ hxw, ?_⟩
    have hpt : (⟨_, heq ▸ hxw⟩ : (U.X k).dom) = ⟨_, hxw⟩ := Subtype.ext heq.symm
    rw [hpt]
    have hlie := Uw.lie k ⟨_, hxw⟩
    refine ⟨hlie.1.trans q1.symm, fun τ i => ?_⟩
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F Ha.i (Ha.Pw w) (Ha.period w hw) (Uw.ik k)
      (Uw.Pm k ⟨_, hxw⟩) L.toLinearMap (Uw.period k _) q2 _ _).2 ?_
    rw [show L.toLinearMap (L.symm (Pi.single (Uw.e.symm ⟨τ, i⟩) 1)) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 from
      L.apply_symm_apply _]
    exact hlie.2 τ i

end GlobalTheory.CuspFrom
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  atlas_forward_decl GlobalTheory.CuspFrom.flowTie_of_onOrbit
end

section
section
noncomputable section

namespace GlobalTheory.CuspFromBasis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
open Matrix GlobalTheory.LieEigen GlobalTheory.ConstBasis
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem exists_comb_of_type {I : Type} {m : I → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : I, Fin (m τ)) (τ : I) {w : Fin g → ℂ}
    (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∃ cf : Fin (m τ) → ℂ, w = ∑ k, cf k • (Pi.single (e.symm ⟨τ, k⟩) 1 : Fin g → ℂ) := by
  refine ⟨fun k => w (e.symm ⟨τ, k⟩), funext fun j => ?_⟩
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  rw [Finset.sum_apply]
  by_cases h : τ' = τ
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne (by simpa using hk.symm), smul_zero]) (by simp)]
    simp
  · have h₀ : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h₁
      exact h (by simpa using hw _ h₁)
    rw [h₀]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h₁ => h (congrArg Sigma.fst (e.symm.injective h₁))), smul_zero]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ArcBasis W (fun τ => σ.comp (embK c τ)) e := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw O _ β Y a χ W Ha e z hσ hz he
  have hG := GlobalTheory.ArcCM.known_holds.laws.globalFns
  obtain ⟨g, e₀, v, M, hev, hv, hu, hM⟩ := ConstLie.exists_const_basis hG E H Dw l Xo c O β Y ℂ _ a χ W
  have lin := ConstLin.lieImg_iff_isLieComb hG E H Dw l Xo c O β Y ℂ _ a χ W
  obtain ⟨an₁, an₂, an₃, an₄⟩ := ExpTan.anVec_bijective hG E H Dw l Xo c σ O β Y a χ W _ _ _ Ha
  have := flat_of_injective ℂ (PowerSeries ℂ) PowerSeries.C_injective
  let ρ : (E →+* ℂ) → 𝓞 E → ℂ := fun τ x => σ (embK c τ x)
  let M' : 𝓞 E → Matrix (Fin g) (Fin g) (PowerSeries ℂ) := fun x => (M x).map (PowerSeries.C (R := ℂ))
  have hM' : ∀ x i, IsLieComb (M' x i) v (v i ≫ W.t.act.act x) := hM
  choose zz hzz using fun i => (an₁ _ (hev i).1).exists
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin Uw.g → ℂ) := Fintype.linearCombination ℂ zz
  have comb : ∀ u ν, GtComb u e₀ ν ↔ AnVec Ha ν (L u) := fun u ν => an₄ g u e₀ zz ν hzz
  have img : ∀ u ν, AnVec Ha ν (L u) → LieImg W ν (prodPts (fun j => PowerSeries.C (R := ℂ) (u j)) v) :=
    fun u ν h => (lin g _ e₀ _ v _ (fun i => (hev i).2) ((comb u ν).2 h)).2 ((Chart.isLieComb_iff _ _ _).2 rfl)
  have inj : Function.Injective L := fun u u' h => by
    obtain ⟨ν, hν, -⟩ := an₂ (L u)
    exact (hu ν (an₃ _ _ hν)).unique ((comb _ _).2 hν) ((comb _ _).2 (h ▸ hν))
  have surj : Function.Surjective L := fun w => by
    obtain ⟨ν, hν, -⟩ := an₂ w
    obtain ⟨u, h, -⟩ := hu ν (an₃ _ _ hν)
    exact ⟨u, (an₁ ν (an₃ _ _ hν)).unique ((comb _ _).1 h) hν⟩
  have cm : ∀ x (u : Fin g → ℂ), (fun j => PowerSeries.C (R := ℂ) (u j)) ᵥ* M' x =
      fun j => PowerSeries.C (R := ℂ) ((u ᵥ* M x) j) := fun x u =>
    funext fun i => ((PowerSeries.C (R := ℂ)).map_vecMul (M x) u i).symm
  have act : ∀ (x : 𝓞 E) u, L (u ᵥ* M x) = fun k => Formalism.L2.PjFree.relab c σ (Uw.e k).1 (x : E) * L u k := fun x u => by
    by_cases hx : x = 0
    · subst hx
      obtain ⟨ρ', hρ'⟩ := exists_action hv W.t.act
      have h₁ := prodPts_injective hv ((hρ' 0 (fun j => PowerSeries.C (R := ℂ) (u j))).trans
        (prodPts_act hv hM' 0 _))
      rw [cm, map_zero] at h₁
      have h₂ : u ᵥ* M 0 = 0 := funext fun j => PowerSeries.C_injective (R := ℂ)
        ((congrFun h₁ j).symm.trans (map_zero _).symm)
      rw [h₂, map_zero]
      funext k
      simp
    · obtain ⟨ν, hν, -⟩ := an₂ (L u)
      obtain ⟨u₁, h₁⟩ := surj fun k => Formalism.L2.PjFree.relab c σ (Uw.e k).1 (x : E) * L u k
      obtain ⟨ν₁, hν₁, -⟩ := an₂ (L u₁)
      have h₂ := ArcType.act_eq Ha hx hν (img _ _ hν) (isTangent_prodPts hv.1 _) (h₁ ▸ hν₁) (img _ _ hν₁)
        (isTangent_prodPts hv.1 _)
      rw [prodPts_act hv hM', cm] at h₂
      have h₃ : u₁ = u ᵥ* M x := funext fun j => PowerSeries.C_injective (R := ℂ)
        (congrFun (prodPts_injective hv h₂) j)
      rw [← h₃, h₁]
  have typ : ∀ τ w, (∀ x, w ᵥ* M x = ρ τ x • w) ↔ ∀ j, L w j ≠ 0 → (Uw.e j).1 = τ := fun τ w => by
    refine ⟨fun h j hj => ?_, fun h x => inj ?_⟩
    · refine (GlobalTheory.Relab.relab_good E H l c σ hσ).1.1 ?_
      refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => ?_)
      have h₁ := congrFun (act x w) j
      rw [h x, map_smul] at h₁
      exact mul_right_cancel₀ hj h₁.symm
    · rw [act, map_smul]
      funext j
      by_cases hj : L w j = 0
      · simp [hj]
      · rw [h j hj]; rfl
  choose u hu using fun τ k => surj (z τ k)
  have imgu : ∀ τ k, LieImg W (e τ k) (prodPts (fun j => PowerSeries.C (R := ℂ) (u τ k j)) v) := fun τ k =>
    img _ _ ((hu τ k).symm ▸ he τ k)
  have eig : ∀ τ k x, u τ k ᵥ* M x = ρ τ x • u τ k := fun τ k =>
    (typ τ _).2 ((hu τ k).symm ▸ (hz τ).2 k)
  have key : ∀ τ (w : Fin g → PowerSeries ℂ), (∀ x, w ᵥ* M' x = PowerSeries.C (R := ℂ) (ρ τ x) • w) →
      ∃! cf : Fin (Dw.mult τ) → PowerSeries ℂ, w = ∑ k, cf k • (fun j => PowerSeries.C (R := ℂ) (u τ k j)) := by
    intro τ
    refine (commonEigenvectors_flat_baseChange ℂ (𝓞 E) g _ M (ρ τ)).1 ℂ (u τ) (eig τ) ?_ (PowerSeries ℂ)
    have : ∀ w : Fin g → ℂ, (∀ x, w ᵥ* M x = ρ τ x • w) →
        ∃! cf : Fin (Dw.mult τ) → ℂ, w = ∑ k, cf k • u τ k := fun w hw => by
      refine (existsUnique_congr fun cf => ?_).1 (LetterBasis.existsUnique_comb (hz τ).1
        (fun k => exists_comb_of_type Uw.e τ ((hz τ).2 k)) (exists_comb_of_type Uw.e τ ((typ τ w).1 hw)))
      rw [← inj.eq_iff, map_sum]
      simp only [map_smul, hu]
    simpa using this
  refine ⟨_, imgu, fun τ => ⟨fun k => ⟨isTangent_prodPts hv.1 _, fun x => ?_⟩, fun w hw he => ?_⟩⟩
  · rw [eig_iff hv hM']
    exact vecMul_map _ (eig τ k x)
  · obtain ⟨d, rfl⟩ := exists_prodPts hv hw
    refine (existsUnique_congr fun cf => ?_).1 (key τ d fun x => (eig_iff hv hM' _ _ _).1 (he x))
    rw [Chart.isLieComb_iff, prodPts_prodPts hv.1, (prodPts_injective hv).eq_iff]

end GlobalTheory.CuspFromBasis
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_vectors_lieBasis_of_complex_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ArcBasis W (fun τ => σ.comp (embK c τ)) e := by
  atlas_forward_decl GlobalTheory.CuspFromBasis.main
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem arc_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  intro E _ _ _ H Dw l Xo c σ O _ β Y a χ W _ e th y hF hχ hβ hB hA hab
  have hι : algebraMap (PowerSeries ℂ) ℂ⸨X⸩ = HahnSeries.ofPowerSeries ℤ ℂ := rfl
  have hFr : algebraMap c.F ℂ⸨X⸩ = ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))).comp σ :=
    RingHom.ext hF
  have hcond : χ ≫ Y.s = spMap ((PowerSeries.C (R := ℂ)).comp σ) ≫ spMap β := by
    rw [hχ, OpenReg.spMap_comp, OpenReg.spMap_comp]
  let χ' : Sp (PowerSeries ℂ) ⟶ gen Y := pullback.lift χ (spMap ((PowerSeries.C (R := ℂ)).comp σ)) hcond
  have hχ'1 : χ' ≫ genι Y = χ := pullback.lift_fst _ _ _
  have hχ'2 : χ' ≫ genStr Y = spMap ((PowerSeries.C (R := ℂ)).comp σ) := pullback.lift_snd _ _ _
  obtain ⟨v, hvL, hv⟩ := hB
  obtain ⟨z, t', m1, m2, φ, hz, hzx, hφ, h0, hm, hu, -⟩ := hA
  have hG : Out.GlobalFnsSt := known_holds.laws.globalFns

  have hzF : z = GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [hzx, Descent.ptF_fst]
    · rw [Descent.ptF_snd]
      apply hβ.right_cancellation
      have e1 : z ≫ pullback.snd _ _ = z ≫ Y.jQ ≫ pullback.snd _ _ := by rw [Y.jQ_over]
      rw [e1, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc z, ← Category.assoc (z ≫ Y.jQ)]
      change (z ≫ Y.j) ≫ Y.s = _
      rw [hz, Category.assoc, hχ, OpenReg.spMap_comp, OpenReg.spMap_comp, OpenReg.spMap_comp, hFr]
  have hw : ∀ τ k, (v τ k).left ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
    fun τ k => (Over.w (v τ k)).trans (Category.comp_id _).symm
  let g : EigFrame Y ((PowerSeries.C (R := ℂ)).comp σ) (χ' ≫ genι Y) :=
    { v := fun τ k => (v τ k).left ≫ W.m.φ
      tan := fun τ k => by
        rw [hχ'1]
        exact (OpenReg.tan_iff W.m (Category.id_comp χ) (hw τ k)).2
          ((DepthExt.tan_iff W.t (v τ k)).1 ((hv τ).1 k).1)
      eig := fun τ k x => by
        exact (OpenReg.eig_iff W.m (hw τ k) x _).2 (((hv τ).1 k).2 x)
      basis := fun τ w htan heig => by
        rw [hχ'1] at htan ⊢
        obtain ⟨w0, hw01, hw02⟩ := OpenReg.exists_lift W.m (spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))))
          w (by rw [htan.1])
        subst hw02
        have hw0 : w0 ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
          hw01.trans (Category.comp_id _).symm
        let W0 : epsR (PowerSeries ℂ) ⟶ W.t.G := Over.homMk w0 hw01
        have t0 : IsTangent W0 := (DepthExt.tan_iff W.t W0).2 ((OpenReg.tan_iff W.m (Category.id_comp χ) hw0).1 htan)
        have e0 : ∀ x : 𝓞 E, (W0 ≫ W.t.act.act x).left =
            spMap (epsScaleR (PowerSeries.C (R := ℂ) ((σ.comp (embK c τ)) x))) ≫ W0.left := fun x =>
          (OpenReg.eig_iff W.m hw0 x _).1 (heig x)
        obtain ⟨cf, hcf, hu1⟩ := (hv τ).2 W0 t0 e0
        refine ⟨cf, ?_, fun cf' hcf' => hu1 cf' ?_⟩
        · exact (OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf hw0).2
            ((DepthExt.comb_iff W.t (v τ) cf W0).1 hcf)
        · exact (DepthExt.comb_iff W.t (v τ) cf' W0).2
            ((OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf' hw0).1 hcf') }
  refine ⟨χ', g, hχ'2, ?_, fun τ k => ?_, ?_⟩
  · rw [← hzF]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hχ'1]
      exact hz
    · rw [Category.assoc, Category.assoc, hχ'2, Y.jQ_over, hzF, Descent.ptF_snd, OpenReg.spMap_comp, hFr]
  · obtain ⟨v1, u', hL, h1, h2, h3⟩ := hu τ k
    obtain rfl : v1 = v τ k := (ConstLie.main hG E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W (e τ k)).1.unique hL (hvL τ k)
    refine ⟨u' ≫ φ, ?_, ?_, ?_⟩
    · rw [Category.assoc, hφ, ← Category.assoc, h3, hzF]
    · rw [Category.assoc, h0, h1]
    · rw [Category.assoc, hm, ← Category.assoc, h2, Category.assoc]
  · rw [mem_genBd_iff]
    rw [← hχ'1] at hab
    exact hab

end GlobalTheory.CuspFrom
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_framed_point_extends_to_model_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  atlas_forward_decl GlobalTheory.CuspFrom.arc_bdExt
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundaryExtension_independent_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  first | exact @GlobalTheory.CuspFrom.bdExt_of_bdExt | exact GlobalTheory.CuspFrom.bdExt_of_bdExt | (intros; apply GlobalTheory.CuspFrom.bdExt_of_bdExt <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_eigFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z R R' _ hR _ _ φ x f ψ
  exact GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z R φ x f hR R' ψ
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenspaceFrame_localRing_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  atlas_forward_decl GlobalTheory.CuspFrom.exists_eigFrame_baseChange
end

section
noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {la : Wt X.Ψ r}
  {P : Frame X.Ψ r → ℂ}

theorem thickBdd (hP : X.IsSec la P) : ThickBdd X (X.pnorm la P) := by
  intro ε hε
  obtain ⟨K, hK, hKd, hcov⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn ((AR.Up.BigB.pnorm_contOn X la hP).mono hKd)).bddAbove
  refine ⟨C, fun x hx hl => ?_⟩
  obtain ⟨γ, hγ, b, hb, h⟩ := hcov x hx hl
  have := hC ⟨_, h, rfl⟩
  rwa [AR.Up.OW.pnorm_lact la hP hγ (AR.Up.OntoS.dom_rmul X hx hb), FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb] at this

theorem freqNonneg (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : FreqNonneg X la P :=
  GlobalTheory.T.koecher_principle_flagDomain_frequencies_nonneg (GlobalTheory.T.flowOrbitFirstMinimum_of_isotropicFlowMajorant GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz) E r X la P hf hP (thickBdd X hP)

theorem growth (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ τ, X.spread la τ / 2 ≤ w) : ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-(A * w)) :=
  GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz E r X w _ hw (fun x _ => mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x))
    (thickBdd X hP) (GlobalTheory.T.maximum_principle_isotropicFlow_rescaledBound E r X la P w hP (freqNonneg X hf hP) h)

theorem isModerate (hf : 1 < Module.finrank ℚ E / 2) (hP : X.IsSec la P) : X.IsModerate la P := by
  obtain ⟨C, A, h⟩ := growth X hf hP (w := ∑ τ, |X.spread la τ / 2|) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun τ => (le_abs_self _).trans (Finset.single_le_sum (f := fun τ => |X.spread la τ / 2|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact ⟨C, _, h⟩

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_input [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ a : ArcIn Dw l (RingHom.id c.F) ℂ σ, ∀ (O : Type) [CommRing O] (β : O →+* c.F),
      FlowTie Uw (a.restrict β) k ξ' x := by
  letI := H.starRing
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, -, hprim, -, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c σ r U Uw k ξ' x 0 0 hσ hU hξ hx
      (fun m _ => ⟨0, by simp, by funext τ i; simp [Data.embV, Data.emb]⟩) (by simp [cc]) (by simp)
      (fun s _ _ => ⟨0, by simp⟩)
  obtain ⟨B, ex, hex⟩ := GlobalTheory.T.exists_principalCMTriple_exponential_of_period E H l DB _ tyB _ hab.2.1 hab.2.2.2.2
  obtain ⟨aC, Λ, hA, h1, h2⟩ := GlobalTheory.T.exists_complex_arc_of_analytic_model_on_flow_orbit E H Dw l Xo c σ r U Uw k ξ' x B hσ hU A gam ξ DB tyB eB ex hO hrk hdvd
    hprim hab hDp hDq hp hq hex
  subst hA
  exact ⟨aC, GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit E H Dw l Xo c σ r U Uw k ξ' x aC Λ hσ hU hξ hx gam ξ hO hξ0 hrk h1 h2⟩

theorem exists_model (Xo : Moduli Dw l) (c : Coeff l) (hr : 1 ≤ Dw.p + Dw.q) :
    ∃ (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
  classical
  have hK := GlobalTheory.ArcCM.known_holds
  obtain ⟨W, hW⟩ := GlobalTheory.GlobalModelGuards.exists_place 2 Nat.prime_two
  have hg : l.GoodAt 2 := by
    have := l.three_le
    rwa [Level.GoodAt, Nat.factorization_eq_zero_of_not_dvd l.odd.not_two_dvd_nat, pow_zero, Nat.div_one]
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l',
      ∃ Y : Model (Xs l) c (c.V W).subtype, Y.N4 ∧ PushInvertible Y.t.G Y.t.PP.L := by
    intro Xs
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY 2 W Nat.prime_two hW
    exact ⟨Y 2 W Nat.prime_two hW ⟨l, c, hg⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rw [Function.update_self] at h
  exact ⟨W, h⟩

theorem coeff_eq_zero {v : PowerSeries ℂ} (hv : v ∈ IsLocalRing.maximalIdeal (PowerSeries ℂ)) {j : ℤ} (hj : j ≤ 0) :
    (algebraMap (PowerSeries ℂ) ℂ⸨X⸩ v).coeff j = 0 := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hv
  rw [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe]
  split_ifs with h0
  · rfl
  · obtain rfl : j = 0 := by omega
    simpa using hv

end Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped LaurentSeries

end GlobalTheory.CuspFrom
end
end
