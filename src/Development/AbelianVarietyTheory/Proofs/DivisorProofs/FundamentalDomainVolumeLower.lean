import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLevelSelfDualLattice

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

open MeasureTheory Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MassFullLevel

theorem levW_le {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) :=
  fun _ hx => ⟨hx.1, Subgroup.mem_top _⟩

theorem relIndex_ne_zero {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) ≠ 0 := by
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (Cl.βW i) (Cl.datWp i P) := by
    have e : Cl.datWp i (LevelP.full _ _ _) = { Cl.datWp i P with P := LevelP.full (Cl.datWp i P).Pg (Cl.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, Formalism.IndefR.Lev.datY, if_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  exact (GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (Cl.βW i) (Cl.datWp i P) _ hB).1

theorem mass_le_of_full : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ∃ μ' : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i)), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ' 𝓕 ∧ μ' 𝓕 ≤ μ 𝓕 := by
  intro D Tu Cl t0 _ i P μ 𝓕 hμ
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelMeasure.exists_isMeasLev D (Wc D i) (Cl.βW i) (Cl.datWp i (LevelP.full Cl.Pg D.R.r ℂ))
    (D.sp.W_sig ((i : ℕ) + 1))
  have hne := relIndex_ne_zero Cl i P
  have hmeas : MeasurableSet {g : GA D (Wc D i) | Formalism.IndefR.Lev.finE (Wc D i) g ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P} := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    exact (GlobalTheory.ParahoricCompact.isOpen_comap_lev (Wc D i) (Cl.βW i) (Cl.datWp i P)).measurableSet
  have e := GlobalTheory.ChainTw.VolScale.scale (Wc D i) (fun _ m => Formalism.IndefR.Lev.IsMinf m) (fun _ _ h => h.1) _ _ μ ν
    (levW_le Cl i P) Formalism.L2.DIV.lev_le_UA hne hmeas hμ.1 hν
  set n : ℝ≥0∞ := ((GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) : ℝ≥0∞)
    with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hne
  have hnt : n ≠ ⊤ := ENNReal.natCast_ne_top _
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  have eν : ν = n⁻¹ • μ := by
    rw [e, smul_smul, ENNReal.inv_mul_cancel hn0 hnt, one_smul]
  refine ⟨ν, ⟨hν, ?_⟩, ?_⟩
  · rw [eν]; exact hμ.2.mono Measure.smul_absolutelyContinuous
  · rw [e, Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le hn1

end GlobalTheory.MassFullLevel
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_level_measure : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ∃ μ' : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i)), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ' 𝓕 ∧ μ' 𝓕 ≤ μ 𝓕 := by
  atlas_forward_decl GlobalTheory.MassFullLevel.mass_le_of_full
end

section
section
noncomputable section

namespace GlobalTheory.SUVol.LieMeasFree

open MeasureTheory Matrix NumberField
open scoped ENNReal
open GlobalTheory.SUVol GlobalTheory.SUVol.DensOne ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.SUVol.LieMeas

theorem riemLie_eq_smul_formLie_of_signs (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (p0 : Ψ → ℕ)
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (_hr : 2 ≤ r) (hG : G.det ≠ 0)
    (ho : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (he : ∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) e) :
    riemLie Ψ G x = ENNReal.ofReal (Real.sqrt
      ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie Ψ e := by
  classical
  set D : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) with hDdef
  have hD : ∀ τ, D τ * D τ = 1 := by
    intro τ
    rw [hDdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext a; unfold sgn; split_ifs <;> simp
  have hDc : ∀ τ, (D τ).map (starRingEnd ℂ) = D τ := by
    intro τ
    rw [hDdef, diagonal_map (map_zero _)]
    congr 1; funext a; simp
  have hxD : ∀ τ, (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) = D τ := fun τ => by
    rw [← gram_eq]; exact ho τ
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ h
    have h1 := congrArg Matrix.det (hxD τ)
    have h2 := congrArg Matrix.det (hD τ)
    rw [det_mul, det_mul, det_transpose, h] at h1
    simp [← h1] at h2
  have hsk : ∀ i, (e i)ᵀ * G + G * (e i).map cc = 0 := fun i => skew_matrix G (he i).2
  have hE : LinearIndependent E e := GlobalTheory.T.real_independent_skew_matrices G hG e hsk hli
  have hR : ∀ τ : Ψ, LinearIndependent ℝ (fun i => (e i).map τ.1) := fun τ => GlobalTheory.T.linear_independent_complex_map τ.1 e hE
  have hmem : ∀ (τ : Ψ) i, ((e i).map τ.1)ᵀ * G.map τ.1 + G.map τ.1 * ((e i).map τ.1).map (starRingEnd ℂ) = 0 ∧
      ((e i).map τ.1).trace = 0 := by
    intro τ i
    refine ⟨map_skew G (hsk i) τ.1, ?_⟩
    have h1 : ((e i).map τ.1).trace = τ.1 (e i).trace := by simp [Matrix.trace, map_sum]
    rw [h1, (he i).1, map_zero]
  have hinj : Function.Injective (coordMap Ψ e) := by
    refine (injective_iff_map_eq_zero (coordMap Ψ e)).2 fun c hc => funext fun τ => funext fun i => ?_
    have h1 := coordMap_apply Ψ e c τ
    rw [hc] at h1
    exact Fintype.linearIndependent_iff.1 (hR τ) (c τ) h1.symm i
  have hsurj : ∀ Z ∈ realLie Ψ G, ∃ c, coordMap Ψ e c = Z := by
    intro Z hZ
    have hX' := (mem_realLie_iff Ψ G Z).1 hZ
    have hspan : ∀ τ : Ψ, Matrix.of (Z τ) ∈ Submodule.span ℝ (Set.range fun i => (e i).map τ.1) :=
      fun τ => GlobalTheory.T.unitary_lie_algebra_spanned (G.map τ.1) (det_map_ne G hG τ.1) _ (hR τ) (hmem τ) _ (hX' τ).1 (hX' τ).2
    choose c hc using fun τ => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan τ)
    refine ⟨c, funext fun τ => ?_⟩
    have h1 := coordMap_apply Ψ e c τ
    rw [hc τ] at h1
    exact h1
  have hin : ∀ c, coordMap Ψ e c ∈ realLie Ψ G := by
    intro c
    refine (mem_realLie_iff Ψ G _).2 fun τ => ?_
    rw [coordMap_apply]
    refine ⟨?_, by simp [trace_sum, (hmem τ _).2]⟩
    have h1 : (∑ i, c τ i • (e i).map τ.1).map (starRingEnd ℂ) =
        ∑ i, c τ i • ((e i).map τ.1).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.sum_apply]
    rw [h1, transpose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hmem τ i).1, smul_zero]
  let f0 : (Ψ → Fin (r ^ 2 - 1) → ℝ) →ₗ[ℝ] (realLie Ψ G).comap (fromFrame x) :=
    ((toFrame x).comp (coordMap Ψ e)).codRestrict _ fun c => by
      change fromFrame x (toFrame x (coordMap Ψ e c)) ∈ realLie Ψ G
      rw [fromFrame_toFrame x hx]; exact hin c
  have hf0 : ∀ c, fromFrame x (f0 c).1 = coordMap Ψ e c := fun c => fromFrame_toFrame x hx _
  have hb : Function.Bijective f0 := by
    refine ⟨fun c d h => hinj (by rw [← hf0, ← hf0, h]), fun Y => ?_⟩
    obtain ⟨c, hc⟩ := hsurj _ Y.2
    refine ⟨c, Subtype.ext ?_⟩
    change toFrame x (coordMap Ψ e c) = Y.1
    rw [hc, toFrame_fromFrame x hx]
  let f := LinearEquiv.ofBijective f0 hb
  let Y : Ψ → Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ := fun τ i => (mat x τ)⁻¹ * (e i).map τ.1 * mat x τ
  have hfY : ∀ τ i σ, Matrix.of (fun a b => (f (Pi.single τ (Pi.single i 1))).1 (σ, a, b)) =
      if σ = τ then Y τ i else 0 := by
    intro τ i σ
    change Matrix.of (fun a b => toFrame x (coordMap Ψ e (Pi.single τ (Pi.single i 1))) (σ, a, b)) = _
    rw [toFrame_apply, coordMap_apply]
    split_ifs with h
    · subst h; simp [Y, Pi.single_apply]
    · simp [h]
  have hgram : (Matrix.of fun p q : Fin (r ^ 2 - 1) × Ψ => inner ℝ (f (Pi.single p.2 (Pi.single p.1 1)))
      (f (Pi.single q.2 (Pi.single q.1 1)))) =
      blockDiagonal fun τ => Matrix.of fun i j => (trace (Y τ i * (Y τ j)ᴴ)).re := by
    ext ⟨i, τ⟩ ⟨j, σ⟩
    rw [Matrix.of_apply, Submodule.coe_inner, inner_eq_sum_trace, blockDiagonal_apply]
    simp only [hfY]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]
  have hYli : ∀ τ, LinearIndependent ℝ (Y τ) := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun g hg => Fintype.linearIndependent_iff.1 (hR τ) g ?_
    have h1 : (mat x τ)⁻¹ * (∑ i, g i • (e i).map τ.1) * mat x τ = 0 := by
      rw [← hg]; simp [Y, Finset.mul_sum, Finset.sum_mul]
    have h2 := congrArg (fun M => mat x τ * M * (mat x τ)⁻¹) h1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h2
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit] at h2
  have htr : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ), trace ((mat x τ)⁻¹ * M * mat x τ) = trace M := by
    intro τ M
    rw [trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hYsk : ∀ τ i, (Y τ i)ᵀ * D τ + D τ * (Y τ i).map (starRingEnd ℂ) = 0 ∧ (Y τ i).trace = 0 := by
    intro τ i
    refine ⟨?_, by rw [htr, (hmem τ i).2]⟩
    have h0 : mat x τ * Y τ i = (e i).map τ.1 * mat x τ := by
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    have h1 := congrArg (fun M => (mat x τ)ᵀ * M * (mat x τ).map (starRingEnd ℂ)) (hmem τ i).1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
    rw [← hxD τ, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, h0, transpose_mul,
      Matrix.mul_assoc _ ((mat x τ).map _), ← Matrix.map_mul, h0, Matrix.map_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hdetτ : ∀ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      (Matrix.of fun i j => trace (Y τ i * Y τ j)).det := by
    intro τ
    rw [RingHom.map_det]
    congr 1
    ext i j
    have h1 : Y τ i * Y τ j = (mat x τ)⁻¹ * ((e i * e j).map τ.1) * mat x τ := by
      rw [Matrix.map_mul]
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    rw [Matrix.of_apply, h1, htr]
    simp [Matrix.trace, map_sum, Matrix.mul_apply]
  have hcF : Continuous fun Z : (realLie Ψ G).comap (fromFrame x) => fromFrame x Z.1 :=
    (fromFrame x).continuous_of_finiteDimensional.comp continuous_subtype_val
  have hcf : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  unfold riemLie
  rw [volume_eq_sqrt_gram_map f, Measure.map_smul, Measure.map_map hcF.measurable hcf.measurable, hgram,
    det_blockDiagonal, Finset.abs_prod, norm_prod]
  congr 3
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdetτ, abs_det_re_trace (D τ) (hD τ) (hDc τ) (Y τ) (hYli τ) (hYsk τ)]
  · funext c
    exact hf0 c

end GlobalTheory.SUVol.LieMeasFree
end
end

open NumberField Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_diagonal_signature_traceless_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → G.det ≠ 0 → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ i, (e i).trace = 0 ∧ ∀ u w, ReciprocityTheory.ChartRestriction.G.FD.herm G (e i *ᵥ u) w + ReciprocityTheory.ChartRestriction.G.FD.herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → GlobalTheory.SUVol.riemLie Ψ G x = ENNReal.ofReal (Real.sqrt ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • GlobalTheory.SUVol.formLie Ψ e := by
  atlas_forward_decl GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs
end

section
section
open NumberField IsDedekindDomain GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.EulerLocVol

theorem locFactor_eq_of_isPrime (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r)
    (hw : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime) :
    locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (-1) ^ i * ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
  classical
  unfold locFactor resOrder
  rw [if_pos hw]
  set w := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hwdef
  set c := IsCMField.ringOfIntegersComplexConj E with hcdef
  have hcc : ∀ x, c (c x) = x := fun x => by
    ext; simp [hcdef]
  have hfix : ∀ a, c (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) = algebraMap _ _ a :=
    fun a => (IsCMField.ringOfIntegersComplexConj_eq_self_iff E _).2 ⟨a, rfl⟩
  have hle : w ≤ w.comap (c : 𝓞 E →+* 𝓞 E) := by
    rw [hwdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c _ ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  have hw0 : w ≠ ⊥ := by
    rw [hwdef, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  haveI hmax : w.IsMaximal := hw.isMaximal hw0
  letI : Field (𝓞 E ⧸ w) := Ideal.Quotient.field w
  haveI : Finite (𝓞 E ⧸ w) := Ideal.finiteQuotientOfFreeOfNeBot w hw0
  let σ : (𝓞 E ⧸ w) →+* (𝓞 E ⧸ w) := Ideal.quotientMap w (c : 𝓞 E →+* 𝓞 E) hle
  have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := fun x => rfl
  letI : StarRing (𝓞 E ⧸ w) :=
    { star := σ
      star_involutive := fun x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        change σ (σ _) = _
        rw [hσ, hσ, hcc]
      star_mul := fun x y => by
        change σ (x * y) = σ y * σ x
        rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hstar : ∀ x, star (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (c x) := hσ
  rw [ncard_image_lifts_eq_card_specialUnitaryGroup w c hstar r]
  set q := Ideal.absNorm v.asIdeal with hq
  have hK : Nat.card (𝓞 E ⧸ w) = q ^ 2 := by
    have h := Ideal.absNorm_algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) v.asIdeal
    rw [← IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two, Ideal.absNorm_apply (Ideal.map _ _),
      Submodule.cardQuot_apply] at h
    exact h
  have hq2 : 2 ≤ q := GlobalTheory.FiniteOrders.two_le_of_card_eq_sq hK
  have hs : ∃ a : 𝓞 E ⧸ w, star a ≠ a := by
    let f : (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) →+* (𝓞 E ⧸ w) :=
      Ideal.quotientMap w (algebraMap _ _) Ideal.le_comap_map
    have hf : ∀ a, f (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w (algebraMap _ _ a) :=
      fun a => rfl
    refine exists_star_ne_of_not_surjective f (fun x => ?_) (fun x => ?_) (fun hsurj => ?_)
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y + c y)).1
        (by change c _ = _; rw [map_add, hcc, add_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_add]⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E (y * c y)).1
        (by change c _ = _; rw [map_mul, hcc, mul_comm])
      exact ⟨Ideal.Quotient.mk _ a, by rw [hf, ha, hstar, map_mul]⟩
    · haveI : Finite (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
      have h1 := Nat.card_le_card_of_surjective f hsurj
      have h2 : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = q := by
        rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hK, h2] at h1
      nlinarith
  have h := GlobalTheory.FiniteOrders.card_specialUnitaryGroup hK hs (Fin r) (Fintype.card_fin r) hr
  have h' := congrArg (Rat.cast : ℚ → ℝ) h
  push_cast at h'
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq0.ne')]

theorem locFactor_nonneg_and_mul_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hr : 1 ≤ r) :
    0 ≤ locFactor E r v ∧
      locFactor E r v * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ 1 := by
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hqdef
  have hq1 : (1 : ℝ) ≤ q := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    rw [hqdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have ht : ∀ i : ℕ, 0 ≤ (q ^ i)⁻¹ ∧ (q ^ i)⁻¹ ≤ 1 := fun i =>
    ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hq1)⟩
  have hg0 : 0 ≤ ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (ht i).2
  have hg1 : ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) ≤ 1 :=
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (ht i).2) fun i _ => sub_le_self _ (ht i).1
  by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
  · rw [locFactor_eq_of_isPrime E r v hr hp, ← hqdef, ← Finset.prod_mul_distrib]
    have hf0 : ∀ i : ℕ, 0 ≤ 1 - (-1) ^ i * (q ^ i)⁻¹ := by
      intro i
      obtain ⟨h0, h1⟩ := ht i
      rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> linarith
    refine ⟨Finset.prod_nonneg fun i _ => hf0 i, ?_⟩
    refine Finset.prod_le_one (fun i _ => mul_nonneg (hf0 i) (sub_nonneg.2 (ht i).2)) fun i _ => ?_
    obtain ⟨h0, h1⟩ := ht i
    rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> nlinarith
  · have heq : locFactor E r v = ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) := by
      let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
      have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
      have hq : (0 : ℝ) < q := by linarith
      unfold locFactor resOrder
      rw [if_neg hp]
      have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
          q ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - (q ^ i)⁻¹) := by
        have := congrArg (fun x : ℚ => (x : ℝ)) h
        push_cast at this
        exact this
      rw [h', ← hqdef, mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]
    rw [heq]
    exact ⟨hg0, mul_le_one₀ hg1 hg0 hg1⟩

theorem tprod_locFactor_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (GlobalTheory.SUVol.locFactor E r) →
      ∏' v, GlobalTheory.SUVol.locFactor E r v ≤
        (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, 0 ≤ locFactor E r v ∧ locFactor E r v * g (Ideal.absNorm v.asIdeal) ≤ 1 :=
    fun v => locFactor_nonneg_and_mul_le_one E r v (by omega)
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      ∏ v ∈ s, locFactor E r v ≤ Z ^ fdeg E := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) := by
      refine Finset.prod_le_prod (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
      refine GlobalTheory.EulerLocVol.inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    have hlow : (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) :=
      calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
        _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
        _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
        _ ≤ _ := s3
        _ = _ := s2.symm
        _ ≤ _ := s1
    have hL0 : 0 ≤ ∏ v ∈ s, locFactor E r v := Finset.prod_nonneg fun v _ => (hloc v).1
    have hprod : (∏ v ∈ s, locFactor E r v) * ∏ v ∈ s, g (Ideal.absNorm v.asIdeal) ≤ 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_one (fun v _ => mul_nonneg (hloc v).1 (g_nonneg _ ?_)) fun v _ => (hloc v).2
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    have hZf : 0 < Z ^ fdeg E := pow_pos hZ _
    have h3 : (∏ v ∈ s, locFactor E r v) * (Z ^ fdeg E)⁻¹ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlow hL0).trans hprod
    rwa [← div_eq_mul_inv, div_le_one hZf] at h3
  exact le_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)

end GlobalTheory.EulerLocVol
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_local_volume_factor_le_zeta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r → Multipliable (GlobalTheory.SUVol.locFactor E r) → ∏' v, GlobalTheory.SUVol.locFactor E r v ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  atlas_forward_decl GlobalTheory.EulerLocVol.tprod_locFactor_le
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

noncomputable section
namespace GlobalTheory.SUVolLower
open IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol
open scoped ENNReal

theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_inReal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable
    (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)
  have hsub : ∀ y : inReal Ψ G Γ, ∃ γ : GL (Fin r) E, embGL Ψ r γ = (y : realSU Ψ G).1 := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨γ, hγ⟩
  choose f hf using hsub
  refine Function.Injective.countable (f := f) fun a b hab => ?_
  apply Subtype.ext; apply Subtype.ext
  rw [← hf a, ← hf b, hab]

theorem tangentHaar_smul {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H] (c : ℝ≥0∞) (hc : c ≠ ⊤) (ν : Measure (ι → Fin r → Fin r → ℂ)) :
    tangentHaar H (c • ν) = c • tangentHaar H ν := by
  unfold tangentHaar
  rw [smul_smul]
  congr 1
  simp only [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  exact ENNReal.limsup_const_mul_of_ne_top hc

theorem covolume_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    [MeasurableConstSMul G α] (ν : Measure α) [SMulInvariantMeasure G α ν] (c : ℝ≥0∞) (hc : c ≠ 0) :
    covolume G α (c • ν) = c * covolume G α ν := by
  by_cases h : HasFundamentalDomain G α ν
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' : IsFundamentalDomain G s (c • ν) := hs.mono (Measure.smul_absolutelyContinuous)
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]
  · have h' : ¬ HasFundamentalDomain G α (c • ν) := by
      rintro ⟨⟨s, hs⟩⟩
      exact h ⟨⟨s, hs.mono (Measure.absolutelyContinuous_smul hc)⟩⟩
    simp [covolume, h, h']

theorem exists_lie_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : SelfDualLat G Λ) :
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨e, he, hli⟩ := GlobalTheory.suLie_finrank_ge G hΛ.1 hΛ.2.1
  choose N hN hmem using fun i => GlobalTheory.DenClear.exists_natSmul_mem_lieLat G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2
  refine ⟨fun i => (N i : E) • e i, hmem, ?_⟩
  let w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ :=
    fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')
  have hw : (fun i => (N i : E) • e i) = w • e := by
    funext i
    ext a b
    simp [w, Algebra.smul_def]
  rw [hw]
  exact hli.units_smul w

theorem riemLie_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ)
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (hr : 2 ≤ r) (hU : Unr E) (hΛ : SelfDualLat G Λ)
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (hx : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (he : ∀ i, e i ∈ lieLat G Λ) (hli : LinearIndependent (maximalRealSubfield E) e) :
    riemLie Ψ G x = ENNReal.ofReal (Real.sqrt r ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E *
      ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ)) •
      formLie Ψ e := by
  rw [GlobalTheory.T.gram_diagonal_signature_traceless_basis E r G Ψ x p0 e hr hΛ.2.1 hx (fun i => ⟨(he i).1, (he i).2.1⟩) hli]
  congr 1
  congr 1
  have h1 := GlobalTheory.cm_type_normSq_prod_eq_abs_norm E Ψ hcm (Matrix.of fun i j => Matrix.trace (e i * e j)).det
  have h2 := GlobalTheory.T.norm_trace_form_det_index E r G Λ e hr hΛ he hli
  have h3 := GlobalTheory.lieLat_relIndex_dual E r G Λ hr hU hΛ
  rw [h3] at h2
  rw [h2] at h1
  push_cast at h1
  have hn : ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖ =
      (r : ℝ) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2 :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hs : Real.sqrt ((r : ℝ) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E) = Real.sqrt r ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow, Real.mul_self_sqrt (by positivity)]
  rw [hn, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hs]

theorem zeta_le_two (i : ℕ) (hi : 2 ≤ i) : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ 2 := by
  have hs2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using this
  have hsi : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hle : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ Real.pi ^ 2 / 6 := by
    rw [← hs2.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hsi hs2.summable
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hi)
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

theorem zprod_le (r : ℕ) : ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ 2 ^ r := by
  calc ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ ∏ _i ∈ Finset.Icc 2 r, (2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => tsum_nonneg fun n => by positivity)
          fun i hi => zeta_le_two i (Finset.mem_Icc.1 hi).1
    _ = 2 ^ (Finset.Icc 2 r).card := Finset.prod_const _
    _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by simp)

theorem sum_covolume_ge : GlobalTheory.Published.TamagawaSpecialUnitary → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) [MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G)] [BorelSpace (GlobalTheory.SUVol.realSU Ψ G)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)), 2 ≤ r → GlobalTheory.UCls.Unr E → GlobalTheory.UCls.SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin r → E)) 1 s → ENNReal.ofReal (c ^ (ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r ^ 2)) ≤ ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin r → E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) := by
  intro hP
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro E _ _ _ r G Λ Ψ x p0 _ _ J s hr hU hΛ hcm hx hs
  obtain ⟨e, he, hli⟩ := exists_lie_basis G Λ hΛ
  obtain ⟨hmult, hP1⟩ := hP E r G Λ Ψ e J s hr hU hΛ hcm he hli hs
  have hlie := riemLie_eq E r G Λ Ψ x p0 e hr hU hΛ hcm hx he hli
  have hPpos := (GlobalTheory.EulerLocVol.tprod_locFactor_bound E r hr hmult).1
  have hPle := GlobalTheory.T.tprod_local_volume_factor_le_zeta E r hr hmult
  set f := ReciprocityTheory.ChartRestriction.G.FD.fdeg E with hf
  set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
    (lieLat G Λ) : ℝ) with hm
  set P : ℝ := ∏' v, locFactor E r v with hPdef
  set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ
  set n : ℝ := (r : ℝ) ^ 2 - 1 with hn
  set μ := tangentHaar (realSU Ψ G) (formLie Ψ e) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ f * m) with hc
  have hD1 : 1 ≤ D := by
    rw [hD]
    have h0 : discr (maximalRealSubfield E) ≠ 0 := discr_ne_zero _
    have : (1 : ℤ) ≤ |discr (maximalRealSubfield E)| := Int.one_le_abs h0
    exact_mod_cast this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero] at hP1
      exact zero_ne_one hP1
  have hr1 : (1 : ℝ) ≤ Real.sqrt r := by
    rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ r)
  have hr0 : 0 < Real.sqrt r := lt_of_lt_of_le one_pos hr1
  have hcpos : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hriem : riemHaar Ψ G x = c • μ := by
    unfold riemHaar
    rw [hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]
  have hcov : ∀ j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G)
      (riemHaar Ψ G x) = c * covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j)))
      (realSU Ψ G) μ := by
    intro j
    haveI := countable_inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))
    rw [hriem, covolume_smul _ _ hcpos]
  simp_rw [hcov]
  rw [ENNReal.tsum_mul_left]
  set S := ∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) μ with hS
  have ha : 0 < D ^ (-n / 2) * m * P := by positivity
  have hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hP1)
  rw [hS1, hc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have key : Real.sqrt r ^ f * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ f * P⁻¹ := by
    rw [neg_div, Real.rpow_neg hDpos.le]
    have : D ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hDpos _).ne'
    field_simp
  rw [key]
  have hn0 : 0 ≤ n / 2 := by
    rw [hn]
    have : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    linarith
  have hDn : 1 ≤ D ^ (n / 2) := Real.one_le_rpow hD1 hn0
  have hsr : 1 ≤ Real.sqrt r ^ f := one_le_pow₀ hr1
  have hZpos : 0 < Z := by
    refine Finset.prod_pos fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs' : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs'.le_tsum 0 (fun j _ => by positivity)
    have h1 : (0 : ℝ) < 1 / (((0 : ℕ) : ℝ) + 1) ^ i := by norm_num
    linarith
  have hPinv : (Z ^ f)⁻¹ ≤ P⁻¹ := inv_anti₀ hPpos hPle
  have hZ2 : Z ^ f ≤ (2 ^ r) ^ f := pow_le_pow_left₀ hZpos.le (zprod_le r) f
  have h2 : ((1 : ℝ) / 2) ^ (f * r ^ 2) ≤ (((2 : ℝ) ^ r) ^ f)⁻¹ := by
    rw [← pow_mul, one_div, inv_pow]
    refine inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) ?_)
    rw [mul_comm r f]
    exact Nat.mul_le_mul_left f (by nlinarith)
  calc ((1 : ℝ) / 2) ^ (f * r ^ 2) ≤ (((2 : ℝ) ^ r) ^ f)⁻¹ := h2
    _ ≤ (Z ^ f)⁻¹ := inv_anti₀ (by positivity) hZ2
    _ ≤ P⁻¹ := hPinv
    _ = 1 * 1 * P⁻¹ := by ring
    _ ≤ D ^ (n / 2) * Real.sqrt r ^ f * P⁻¹ := by
        gcongr

end GlobalTheory.SUVolLower
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_volume_family : GlobalTheory.Published.TamagawaSpecialUnitary → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) [MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G)] [BorelSpace (GlobalTheory.SUVol.realSU Ψ G)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)), 2 ≤ r → GlobalTheory.UCls.Unr E → GlobalTheory.UCls.SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin r → E)) 1 s → ENNReal.ofReal (c ^ (ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r ^ 2)) ≤ ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin r → E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) := by
  atlas_forward_decl GlobalTheory.SUVolLower.sum_covolume_ge
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

namespace GlobalTheory.MassLower

theorem mass_lower : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ENNReal.ofReal (Real.exp (-(C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|)))) ≤ μ 𝓕 := by
  intro hP
  obtain ⟨c1, hc1, hc1', hB⟩ := GlobalTheory.T.full_level_self_dual_lattice
  obtain ⟨c2, hc2, hc2', hS⟩ := GlobalTheory.T.special_unitary_volume_family hP.p6
  have hc : 0 < c1 * c2 := mul_pos hc1 hc2
  have hcle : c1 * c2 ≤ 1 := mul_le_one₀ hc1' hc2.le hc2'
  refine ⟨-Real.log (c1 * c2), neg_nonneg.2 (Real.log_nonpos hc.le hcle), ?_⟩
  intro D Tu Cl t0 hC i P μ 𝓕 hF
  obtain ⟨μ', hF', hle⟩ := GlobalTheory.T.exists_full_level_measure D Tu Cl t0 hC i P μ 𝓕 hF
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨G, Λ, Ψ, x, p0, J, s, h2, hU, hSD, hΨ, hx, hs, hf, hb⟩ := hB D Tu Cl t0 hC i μ' 𝓕 hF'
  letI : MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G) := borel _
  haveI : BorelSpace (GlobalTheory.SUVol.realSU Ψ G) := ⟨rfl⟩
  have hsu := hS D.host.E D.R.r G Λ Ψ x p0 J s h2 hU hSD hΨ hx hs
  rw [hf] at hsu
  set N : ℕ := D.R.f * D.R.r ^ 2 with hN
  have hlogd : 0 ≤ Real.log |(discr D.host.E : ℝ)| := by
    apply Real.log_nonneg
    have h0 : (discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
    have : (1 : ℝ) ≤ |(discr D.host.E : ℤ)| := by
      exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
    simpa using this
  have hlog3 : 0 ≤ Real.log ((D.R.f : ℝ) * D.R.r + 3) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
    linarith
  have hNr : ((N : ℕ) : ℝ) = (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by rw [hN]; push_cast; ring
  have hC0 : 0 ≤ -Real.log (c1 * c2) := neg_nonneg.2 (Real.log_nonpos hc.le hcle)
  have key : Real.exp (-(-Real.log (c1 * c2) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|))) ≤ c1 ^ N * c2 ^ N := by
    have e : (c1 * c2) ^ N = Real.exp (N * Real.log (c1 * c2)) := by rw [Real.exp_nat_mul, Real.exp_log hc]
    rw [← mul_pow, e]
    apply Real.exp_le_exp.2
    rw [hNr]
    have hA : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)| := by
      have : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
      nlinarith
    have hl : Real.log (c1 * c2) ≤ 0 := Real.log_nonpos hc.le hcle
    have := mul_le_mul_of_nonpos_left hA hl
    linarith
  calc ENNReal.ofReal (Real.exp (-(-Real.log (c1 * c2) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|))))
      ≤ ENNReal.ofReal (c1 ^ N * c2 ^ N) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (c1 ^ N) * ENNReal.ofReal (c2 ^ N) := ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (c1 ^ N) * ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) := by
        gcongr
    _ ≤ μ' 𝓕 := hb
    _ ≤ μ 𝓕 := hle

end GlobalTheory.MassLower
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_volume_lower : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ENNReal.ofReal (Real.exp (-(C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|)))) ≤ μ 𝓕 := by
  atlas_forward_decl GlobalTheory.MassLower.mass_lower
end
