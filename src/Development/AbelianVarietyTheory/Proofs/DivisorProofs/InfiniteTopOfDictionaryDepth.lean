import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputsStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open Classical in

private theorem meanInf_avg_le (K M : Type) [Field K] [NumberField K] [Field M] [Algebra ℚ M] [FiniteDimensional ℚ M]
    (i : K →+* M) (h : (M →ₐ[ℚ] ℂ) → ℝ) (h0 : ∀ ρ, 0 ≤ h ρ) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun p => (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}, h ρ) /
      Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}) ≤
      2 * ((∑ ρ, h ρ) / (Module.finrank ℚ M : ℝ)) := by
  letI : Algebra K M := i.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  have hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M := by
    intro σ
    have h1 := GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)
    rw [Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole] at h1
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun ρ _ => ?_
    rw [AlgHom.ext_iff]
    rfl
  have hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ := by
    intro σ
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext ρ
    simp [RingHom.ext_iff]
  have hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤
      ∑ ρ, h ρ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]
    have hinj : Function.Injective (fun p : InfinitePlace K => p.embedding) := fun p q hpq => by
      rw [← p.mk_embedding, ← q.mk_embedding]
      exact congrArg _ hpq
    rw [← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding)
      (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ)
      (fun p _ q _ hpq => hinj hpq)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hk : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  simp only [hcard, hsum]
  rw [← Finset.sum_div, ← ht]
  generalize (∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *
  calc _ = 2 * (S / (Module.finrank ℚ K * Module.finrank K M : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le : ∃ C1 : ℝ, 0 < C1 ∧ ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hArea D δ t0)) ≤ C1 * L ∧ Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hTh D δ t0)) ≤ C1 * L := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hI δ t0 hc ht L hL hrL hdL
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have h2 : g2 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h3 : g3 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h4 : wpF (lat D δ) t0 ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  haveI : FiniteDimensional ℚ (fld D δ t0) := by
    let b := Module.finBasis ℚ D.what₂.LL
    obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
      (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
      ((Set.finite_range _).union (Set.toFinite _)) (by
        rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
        · exact mem_algebraicClosure_iff.2
            ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
        · exact hdata.2.1
        · exact hdata.2.2
        · exact hwp)
    have hle : fld D δ t0 ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro y (⟨y, rfl⟩ | hy)
      · rw [← b.sum_repr y, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
      · exact hM _ (Or.inr hy)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ) := fun ρ => by
    have h := (hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3
    unfold tc
    rw [dif_pos h]
    exact h.choose_spec
  obtain ⟨hu, hv⟩ := hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt
  let i : D.what₂.LL →+* fld D δ t0 := D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)
  refine ⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_,
    (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu zero_le_two
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv zero_le_two
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty : ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ σ : D.what₂.LL →+* ℂ, (ext D δ t0 σ).Finite ∧ (ext D δ t0 σ).Nonempty := by
  first | exact @GlobalTheory.KerConjMean.ext_finite_nonempty | exact GlobalTheory.KerConjMean.ext_finite_nonempty | (intros; apply GlobalTheory.KerConjMean.ext_finite_nonempty <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalEqualSignKernels_largeConstants : BigC fun _ ch _ _ => RatTopAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratTopAt_big | exact GlobalTheory.KerConjMean.ratTopAt_big | (intros; apply GlobalTheory.KerConjMean.ratTopAt_big <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
    1 ≤ Real.log large₂.sc.b ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b ∧ |logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS
  obtain ⟨-, hSz, -, -, -, -, -, -, -, hrd, hcond, -⟩ := hS.size
  have hb : Real.log large₂.sc.b = large₂.sc.x ^ large₂.sc.eps := by
    simp [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L]
  have hL1 : 1 ≤ large₂.sc.x ^ large₂.sc.eps := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hqd : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps := hSz.2.2.2.2.2.2.1.2.2.2.2.2.1
  have he : large₂.logDerivativeAtOne = logDerivativeAtOne D := by
    rw [large₂.logDerivative_at_one_eq]
    rfl
  rw [hb]
  refine ⟨hL1, ?_, he ▸ hqd⟩
  have : Real.log D.host.rdE ≤ large₂.sc.L / 100 := hrd.trans hcond
  simp only [Formalism.BasicNotions.Scale.L] at this
  linarith

theorem meanInf_affine (K : Type) [Field K] [NumberField K] (a0 nD Gd : ℝ) (f g : InfinitePlace K → ℝ) (ha0 : 0 ≤ a0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => a0 + nD * f v + Gd * g v) ≤
      2 * a0 + nD * Formalism.PairingDivisionLocalBalance.meanInf K f + Gd * Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≤ Module.finrank ℚ K := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    exact_mod_cast (by omega : Fintype.card (InfinitePlace K) ≤ Module.finrank ℚ K)
  have h3 : 2 / (Module.finrank ℚ K : ℝ) * ((Fintype.card (InfinitePlace K) : ℝ) * a0) ≤ 2 * a0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith
  nlinarith [h3]

theorem exists_avg {α : Type} (S : Set α) (hS : S.Finite) (hne : S.Nonempty) (a0 nD Gd : ℝ) (h1 h2 : α → ℝ) :
    (∃ ρ ∈ S, a0 + nD * h1 ρ + Gd * h2 ρ ≤
      a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S)) ∧
    (∃ ρ ∈ S, a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) ≤
      a0 + nD * h1 ρ + Gd * h2 ρ) := by
  set s := hS.toFinset with hs
  have hsne : s.Nonempty := by rwa [hs, Set.Finite.toFinset_nonempty]
  have hcard : (Nat.card S : ℝ) = s.card := by
    rw [hs, Nat.card_eq_card_finite_toFinset hS]
  have hs1 : ∑ᶠ ρ ∈ S, h1 ρ = ∑ ρ ∈ s, h1 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hs2 : ∑ᶠ ρ ∈ S, h2 ρ = ∑ ρ ∈ s, h2 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hc0 : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  set m := a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) with hm
  have key : ∑ ρ ∈ s, (a0 + nD * h1 ρ + Gd * h2 ρ) = ∑ _ρ ∈ s, m := by
    rw [Finset.sum_const, nsmul_eq_mul, hm, hs1, hs2, hcard, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp
  constructor
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.le
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.ge
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩

theorem infTopK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨CF0, hCF⟩ := GlobalTheory.T.conjugate_top_bound_of_inputs hP hI hD hDp C1 hC1
  obtain ⟨CF0', hCF'⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  refine ⟨max CF0 CF0', fun CF hCF0 => ?_⟩
  obtain ⟨C0, hC0⟩ := hCF CF (le_trans (le_max_left _ _) hCF0)
  obtain ⟨C0', hC0'⟩ := hCF' CF (le_trans (le_max_right _ _) hCF0)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := hC0 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x0', hx0'⟩ := hC0' ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x0 x0', fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  obtain ⟨a0, nD, Gd, ha0, hnD, hGd, hsum, hbound⟩ :=
    hx0 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  have hrat := hx0' D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  refine ⟨fun p => a0 + nD * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    Gd * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · refine (meanInf_affine _ a0 nD Gd _ _ ha0).trans (le_trans ?_ hsum)
    have e1 := mul_le_mul_of_nonneg_left hmA hnD
    have e2 := mul_le_mul_of_nonneg_left hmT hGd
    nlinarith
  · intro p Φ β d hocc c j B v hv
    obtain ⟨f, hf⟩ := hrat Φ β d hocc c j
    obtain ⟨u, rfl, hu⟩ := hv
    refine ⟨f u, (hf u).symm, ?_⟩
    obtain ⟨hfin, hne⟩ := GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 p.embedding
    obtain ⟨⟨ρ₁, hρ₁, h₁⟩, ⟨ρ₂, hρ₂, h₂⟩⟩ := exists_avg _ hfin hne a0 nD Gd
      (hArea D ch.S.Z.δ ch.S.Z.t0) (hTh D ch.S.Z.δ ch.S.Z.t0)
    rcases le_or_gt 0 B with hB | hB
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₁ hρ₁ u B hu).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h₁) hB)
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₂ hρ₂ u B hu).trans
        (mul_le_mul_of_nonpos_right (Real.exp_le_exp.2 h₂) hB.le)

end GlobalTheory.KerConjMean
end
end
