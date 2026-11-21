import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMapProdEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
import BuildAid.ForwardExisting
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Closed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilpotentOfStrict
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarFrameStabiliserCompatibleFibre
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimilitudeConjPreservesUnitaryHaarAtFinitePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomain

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.MeasWord

theorem exists_measW_prescribed :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r)
      (T : F), P.IsStd σ J T → ∀ (μNinf : Measure (Nsub (Ainf F) σ J P))
      (μHinf : Measure (Hsub (Ainf F) σ J P)) (μN : Measure (Nsub (AF F) σ J P))
      (μH : Measure (Hsub (AF F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μN = μN ∧ W.μH = μH ∧
        W.μSv = μSv := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP μNinf μHinf μN μH μSv hNinf hHinf hN hH hSv
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := PI.UnitaryGroupMassFormula.MeasWCore.hermitian_measure_splitting F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := PI.UnitaryGroupMassFormula.MeasWCore.nilpotent_measure_splitting F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (PI.UnitaryGroupMassFormula.MeasWCore.continuous_measure_splitting F E σ n J hCM).measurable
  have : SecondCountableTopology (Hsub (AF F) σ J P) :=
    eH.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Nsub (AF F) σ J P) :=
    eN.toHomeomorph.symm.isEmbedding.secondCountableTopology
  obtain ⟨μHf, hHf, hHeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eH μHinf μH
  obtain ⟨μNf, hNf, hNeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eN μNinf μN
  obtain ⟨μSf, hSH, hSeq⟩ := PI.UnitaryGroupMassFormula.MeasWCore.product_decomposition_holds F E σ n J r P T hCM hJ hP μNf μHf hNf hHf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := μH, μHinf := μHinf, μHf := μHf, μN := μN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := μSv }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hH, hHinf, hHf, hN, hNinf, hNf, hSH, hSv, ?_, ?_, hSeq⟩
  · show (μH.map Subtype.val).map (splitA σ J) = _
    rw [← hHeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · show (μN.map Subtype.val).map (splitA σ J) = _
    rw [← hNeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end GlobalTheory.St.MeasWord
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem omT_stab_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ a ha1 ha2 X0 hT hdet μ hμ
  obtain ⟨νX, hν⟩ := PI.VolStabS.Assembly.exOmT_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μ', hμ'H, hμ'C⟩ := PI.VolStabS.exStab_of_nu PI.VolStabS.Assembly.nuInv_holds
    PI.VolStabS.nuFin_holds
    (PI.VolStabS.nuNeZero_of_dens PI.VolStabS.archPos_holds PI.VolStabS.locPos_holds
      (PI.VolStabS.densAA_of_open PI.VolStabS.volAA_holds PI.VolStabS.hensAA_holds
        PI.VolStabS.idxH_holds PI.VolStabS.cntAA_holds) PI.VolStabS.qvSum_holds)
    F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  exact ⟨νX, μ', hν, hμ'H, hμ'C⟩

end GlobalTheory
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  atlas_forward_decl GlobalTheory.omT_stab_exist
end

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.NondegTuple

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem exists_tuple_gram_det_ne_zero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ a : ℕ, a ≤ n → ∃ X0 : Fin a → Fin n → E, (gramE σ J X0).det ≠ 0 ∧
        ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j := by
  intro F E _ _ _ _ _ σ hσ n J hJ a ha
  have hc : ∀ t, (σ : E →+* E) ((σ : E →+* E) t) = t := conj_conj hσ
  obtain ⟨P, d, -, hd, hfix, hne⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    (G := J) two_ne_zero hc (fun i j => hJ.1 j i)
  have hg : gramE σ J (fun i k => σ (P k (Fin.castLE ha i))) =
      Matrix.diagonal fun i => d (Fin.castLE ha i) := by
    ext i j
    have h1 := congrFun (congrFun hd (Fin.castLE ha i)) (Fin.castLE ha j)
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply,
      GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum] at h1
    have h2 : Matrix.diagonal d (Fin.castLE ha i) (Fin.castLE ha j) =
        Matrix.diagonal (fun i => d (Fin.castLE ha i)) i j := by
      simp only [Matrix.diagonal_apply, (Fin.castLE_injective ha).eq_iff]
    rw [← h2, ← h1]
    simp only [gramE, hE, Formalism.UG.hform, RingHom.coe_coe, conj_conj hσ]
  refine ⟨fun i k => σ (P k (Fin.castLE ha i)), ?_, ?_⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne hJ.2 _
  · intro i j
    rw [hg]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hfix _
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero]

end GlobalTheory.NondegTuple
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibre

theorem dX_dT_omFam :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ v a ha1 ha2
  obtain ⟨X0, hdet, hT⟩ := GlobalTheory.NondegTuple.exists_tuple_gram_det_ne_zero F E σ hE n J hJ a (by omega)
  have hI : PI.VolStabS.FibInfEx :=
    PI.VolStabS.fibInfEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densInf_holds
  have hV : PI.VolStabS.FibVEx :=
    PI.VolStabS.fibVEx_of PI.VolStabS.DiscreteGroups.fibOfDens_holds PI.VolStabS.tensAll_holds
      PI.VolStabS.densV_holds
  obtain ⟨_, _, μv, νv, _, _, _, _, hμv, hνv, _, _⟩ :=
    PI.VolStabS.locEx_of hI hV PI.VolStabS.latSB_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet
      ψ hψ
  have hX : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨_, hμv v⟩
  have hH : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨_, hνv v⟩
  have hdX : SdW F E σ n J (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dX σ J ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dX
    rw [dif_pos hX]
    exact hX.choose_spec
  have hdT : SdHerm F E σ (Fv F v) (psiV F ψ v) a (Formalism.L2.SG.LocVol.dT σ ψ v a) := by
    unfold Formalism.L2.SG.LocVol.dT
    rw [dif_pos hH]
    exact hH.choose_spec
  have hO : ∃ fib, Formalism.L2.SG.LocVol.IsOm σ J ψ v a fib :=
    hV F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v _ hdX _ hdT
  refine ⟨hdX.1, hdT.1, ?_⟩
  unfold Formalism.L2.SG.LocVol.omFam
  rw [dif_pos hO]
  exact hO.choose_spec

end GlobalTheory.LocalFibre
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, 1 ≤ a → 2 * a < n → (Formalism.L2.SG.LocVol.dX σ J ψ v a).IsAddHaarMeasure ∧ (Formalism.L2.SG.LocVol.dT σ ψ v a).IsAddHaarMeasure ∧ Formalism.L2.SG.LocVol.IsOm σ J ψ v a (Formalism.L2.SG.LocVol.omFam σ J ψ v a) := by
  atlas_forward_decl GlobalTheory.LocalFibre.dX_dT_omFam
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.UnitriSection

open Matrix

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hf_add_l (x y z : Fin n → A) :
    Formalism.UG.hform s J (x + y) z = Formalism.UG.hform s J x z + Formalism.UG.hform s J y z := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hf_smul_l (c : A) (x z : Fin n → A) :
    Formalism.UG.hform s J (c • x) z = s c * Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hf_add_r (x y z : Fin n → A) :
    Formalism.UG.hform s J x (y + z) = Formalism.UG.hform s J x y + Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hf_smul_r (c : A) (x z : Fin n → A) :
    Formalism.UG.hform s J x (c • z) = c * Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_sum_l {ι : Type} (t : Finset ι) (c : ι → A) (x : ι → Fin n → A) (z : Fin n → A) :
    Formalism.UG.hform s J (∑ i ∈ t, c i • x i) z = ∑ i ∈ t, s (c i) * Formalism.UG.hform s J (x i) z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Formalism.UG.hform]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_l, hf_smul_l, ih]

theorem hf_symm (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → A) :
    s (Formalism.UG.hform s J x y) = Formalism.UG.hform s J y x := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

def row (u : Fin n → A) : Fin n → A := Matrix.vecMul (s ∘ u) J

theorem row_dot (u x : Fin n → A) : row s J u ⬝ᵥ x = Formalism.UG.hform s J u x := by
  rw [row, ← Matrix.dotProduct_mulVec, Formalism.UG.P.hform_eq_dot]

def eich (u w : Fin n → A) (c : A) : Matrix (Fin n) (Fin n) A :=
  1 + Matrix.vecMulVec w (row s J u) + Matrix.vecMulVec u (c • row s J u - row s J w)

theorem eich_mulVec (u w : Fin n → A) (c : A) (x : Fin n → A) :
    eich s J u w c *ᵥ x = x + Formalism.UG.hform s J u x • w
      + (c * Formalism.UG.hform s J u x - Formalism.UG.hform s J w x) • u := by
  simp only [eich, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, sub_dotProduct,
    smul_dotProduct, row_dot, smul_eq_mul, op_smul_eq_smul]

theorem eich_unitary (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (u w : Fin n → A)
    (c : A) (huu : Formalism.UG.hform s J u u = 0) (huw : Formalism.UG.hform s J u w = 0)
    (hc : c + s c + Formalism.UG.hform s J w w = 0) :
    Formalism.UG.cT s (eich s J u w c) * J * eich s J u w c = J := by
  have hwu : Formalism.UG.hform s J w u = 0 := by rw [← hf_symm s J hs hJ, huw, map_zero]
  have key : ∀ x y, Formalism.UG.hform s J (eich s J u w c *ᵥ x) (eich s J u w c *ᵥ y)
      = Formalism.UG.hform s J x y := by
    intro x y
    have hxu : Formalism.UG.hform s J x u = s (Formalism.UG.hform s J u x) := (hf_symm s J hs hJ u x).symm
    have hxw : Formalism.UG.hform s J x w = s (Formalism.UG.hform s J w x) := (hf_symm s J hs hJ w x).symm
    rw [eich_mulVec, eich_mulVec]
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_sub, map_mul, huu, huw, hwu, hxu, hxw]
    linear_combination (s (Formalism.UG.hform s J u x) * Formalism.UG.hform s J u y) * hc
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  rw [Formalism.UG.P.hform_mulVec, Formalism.UG.P.hform_single, Formalism.UG.P.hform_single] at this
  exact this

end Alg

section Frame

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_invol (hσ : ∀ e, σ (σ e) = e) (a : R ⊗[F] E) : sigR R σ (sigR R σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem JR_herm (hJ : IsHermND σ J) (i j : Fin n) : sigR R σ (JR R J j i) = JR R J i j := by
  simp only [JR, Matrix.map_apply, sigR_inclR, hJ.1 i j]

theorem h_rat (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  simp [Formalism.UG.hform, hE, ratV, JR, map_sum, map_mul, sigR_inclR]

variable {r : ℕ}

def coef (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (b a : Fin (r + 1)) :
    R ⊗[F] E := if h : a < b then x ⟨(a, b), h⟩ else 0

theorem coef_last (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (b : Fin (r + 1)) :
    coef R x b (Fin.last r) = 0 := by
  simp [coef, not_lt.2 (Fin.le_last b)]

def yv (P : Frame E n r) (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E)
    (b : Fin (r + 1)) : Fin n → R ⊗[F] E :=
  ∑ a, coef R x b a • ratV (F := F) R (F0 P a)

def wv (P : Frame E n r) (T : F) (b : Fin (r + 1)) : Fin n → R ⊗[F] E :=
  Fin.lastCases (inclR (F := F) R (algebraMap F E T⁻¹) • ratV (F := F) R P.z)
    (fun i => (-1 : R ⊗[F] E) • ratV (F := F) R (P.f i)) b

def cc (T : F) (b : Fin (r + 1)) : R ⊗[F] E :=
  Fin.lastCases (inclR (F := F) R (algebraMap F E (2 * T)⁻¹)) (fun _ => 0) b

end Frame

section Facts

variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) (T : F)

variable {R σ J P T}

theorem frameInitialVectors_castSucc (i : Fin r) : F0 P (Fin.castSucc i) = P.e i := by simp [F0]
theorem frameInitialVectors_last : F0 P (Fin.last r) = P.z := by simp [F0]

theorem hE_symm (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (x y : Fin n → E) :
    σ (hE σ J x y) = hE σ J y x :=
  hf_symm (σ : E →+* E) J hσ hJ.1 x y

theorem hermitianFormE_frameE_initialVectors (hP : P.IsStd σ J T) (i : Fin r) (c : Fin (r + 1)) : hE σ J (P.e i) (F0 P c) = 0 := by
  induction c using Fin.lastCases with
  | last => rw [frameInitialVectors_last]; exact hP.2.2.2.1 i
  | cast k => rw [frameInitialVectors_castSucc]; exact hP.1 i k

theorem hermitianFormE_frameZ_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (c : Fin (r + 1)) :
    hE σ J P.z (F0 P c) = if c = Fin.last r then algebraMap F E (-T) else 0 := by
  induction c using Fin.lastCases with
  | last => rw [frameInitialVectors_last, if_pos rfl]; exact hP.2.2.2.2.2.1
  | cast k =>
    rw [frameInitialVectors_castSucc, if_neg (Fin.castSucc_ne_last k), ← hE_symm hσ hJ, hP.2.2.2.1 k, map_zero]

theorem hermitian_flag_dual_basis (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (j : Fin r)
    (c : Fin (r + 1)) : hE σ J (P.f j) (F0 P c) = if c = Fin.castSucc j then 1 else 0 := by
  induction c using Fin.lastCases with
  | last => rw [frameInitialVectors_last, if_neg (Fin.castSucc_ne_last j).symm]; exact hP.2.2.2.2.1 j
  | cast k =>
    rw [frameInitialVectors_castSucc, ← hE_symm hσ hJ, hP.2.2.1 k j]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Fin.castSucc_inj]

local notation "hA" => Formalism.UG.hform (sigR R σ) (JR R J)

variable (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E)

theorem yv_perp (hP : P.IsStd σ J T) (b c : Fin (r + 1)) :
    hA (yv R P x b) (ratV (F := F) R (F0 P c)) = 0 := by
  unfold yv
  rw [hf_sum_l]
  refine Finset.sum_eq_zero fun a _ => ?_
  induction a using Fin.lastCases with
  | last => rw [coef_last, map_zero, zero_mul]
  | cast i => rw [frameInitialVectors_castSucc, h_rat, hermitianFormE_frameE_initialVectors hP, map_zero, mul_zero]

theorem yv_iso (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b : Fin (r + 1)) :
    hA (yv R P x b) (yv R P x b) = 0 := by
  have h1 := hf_sum_l (sigR R σ) (JR R J) Finset.univ (coef R x b)
    (fun a => ratV (F := F) R (F0 P a)) (yv R P x b)
  rw [show hA (yv R P x b) (yv R P x b) = hA (∑ a, coef R x b a • ratV (F := F) R (F0 P a)) (yv R P x b)
    from rfl, h1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← hf_symm _ _ (sigR_invol R σ hσ) (fun i j => JR_herm R σ J hJ i j), yv_perp x hP, map_zero, mul_zero]

theorem yv_w (hP : P.IsStd σ J T) (b : Fin (r + 1)) : hA (yv R P x b) (wv R P T b) = 0 := by
  induction b using Fin.lastCases with
  | last =>
    simp only [wv, Fin.lastCases_last]
    rw [hf_smul_r, ← frameInitialVectors_last (P := P), yv_perp x hP, mul_zero]
  | cast j =>
    simp only [wv, Fin.lastCases_castSucc]
    rw [hf_smul_r]
    unfold yv
    rw [hf_sum_l, Finset.sum_eq_zero, mul_zero]
    intro a _
    induction a using Fin.lastCases with
    | last => rw [coef_last, map_zero, zero_mul]
    | cast i =>
      by_cases hij : Fin.castSucc i < Fin.castSucc j
      · rw [frameInitialVectors_castSucc, h_rat, hP.2.2.1 i j, if_neg (ne_of_lt (Fin.castSucc_lt_castSucc_iff.1 hij)),
          map_zero, mul_zero]
      · simp [coef, hij]

theorem cc_cond (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b : Fin (r + 1)) :
    cc R T b + sigR R σ (cc R T b) + hA (wv R P T b) (wv R P T b) = 0 := by
  induction b using Fin.lastCases with
  | last =>
    simp only [wv, cc, Fin.lastCases_last]
    rw [hf_smul_l, hf_smul_r, h_rat, hP.2.2.2.2.2.1]
    simp only [sigR_inclR, AlgHom.commutes]
    have hT := hP.2.2.2.2.2.2
    have h0 : (2 * T)⁻¹ + (2 * T)⁻¹ + T⁻¹ * (T⁻¹ * -T) = 0 := by
      field_simp
      ring
    have h1 := congrArg (fun t => inclR (F := F) R (algebraMap F E t)) h0
    simp only [map_add, map_mul, map_neg, map_zero] at h1 ⊢
    linear_combination h1
  | cast j =>
    simp only [wv, cc, Fin.lastCases_castSucc]
    rw [hf_smul_l, hf_smul_r, h_rat, hP.2.1 j j]
    simp

theorem unitriangularEichlerSecondVector_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b c : Fin (r + 1)) :
    hA (wv R P T b) (ratV (F := F) R (F0 P c)) = -(if c = b then 1 else 0) := by
  induction b using Fin.lastCases with
  | last =>
    simp only [wv, Fin.lastCases_last]
    rw [hf_smul_l, h_rat, hermitianFormE_frameZ_initialVectors hσ hJ hP, sigR_inclR, AlgHom.commutes]
    by_cases hc : c = Fin.last r
    · rw [if_pos hc, if_pos hc, ← map_mul, ← map_mul, mul_neg, inv_mul_cancel₀ hP.2.2.2.2.2.2]
      simp
    · rw [if_neg hc, if_neg hc]; simp
  | cast j =>
    simp only [wv, Fin.lastCases_castSucc]
    rw [hf_smul_l, h_rat, hermitian_flag_dual_basis hσ hJ hP]
    by_cases hc : c = Fin.castSucc j
    · rw [if_pos hc, if_pos hc]; simp
    · rw [if_neg hc, if_neg hc]; simp

end Facts

section Product

variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) (T : F)

def Mb (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (b : Fin (r + 1)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  eich (sigR R σ) (JR R J) (yv R P x b) (wv R P T b) (cc R T b)

def Pm (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (k : ℕ) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  Nat.rec (motive := fun _ => Matrix (Fin n) (Fin n) (R ⊗[F] E)) 1
    (fun k M => (if h : k < r + 1 then Mb R σ J P T x ⟨k, h⟩ else 1) * M) k

theorem Pm_zero (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) :
    Pm R σ J P T x 0 = 1 := rfl

theorem Pm_succ (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E) (k : ℕ) :
    Pm R σ J P T x (k + 1) = (if h : k < r + 1 then Mb R σ J P T x ⟨k, h⟩ else 1) * Pm R σ J P T x k := rfl

variable {R σ J P T}
variable (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E)

theorem unitriangularColumnEichlerMatrix_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (b c : Fin (r + 1)) :
    Mb R σ J P T x b *ᵥ ratV (F := F) R (F0 P c) =
      ratV (F := F) R (F0 P c) + (if c = b then yv R P x b else 0) := by
  rw [Mb, eich_mulVec, yv_perp x hP, unitriangularEichlerSecondVector_initialVectors hσ hJ hP]
  by_cases h : c = b
  · simp [h]
  · simp [h]

theorem Mb_fix (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (k c : Fin (r + 1))
    (hck : c ≤ k) : Mb R σ J P T x k *ᵥ yv R P x c = yv R P x c := by
  show Mb R σ J P T x k *ᵥ (∑ a, coef R x c a • ratV (F := F) R (F0 P a)) =
    ∑ a, coef R x c a • ratV (F := F) R (F0 P a)
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_smul, unitriangularColumnEichlerMatrix_initialVectors x hσ hJ hP]
  by_cases ha : a = k
  · subst ha
    have : coef R x c a = 0 := by simp [coef, not_lt.2 hck]
    simp [this]
  · simp [ha]

theorem unitriangularEichlerPartialProduct_initialVectors (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (k : ℕ) (c : Fin (r + 1)) :
    Pm R σ J P T x k *ᵥ ratV (F := F) R (F0 P c) =
      ratV (F := F) R (F0 P c) + (if c.val < k then yv R P x c else 0) := by
  induction k with
  | zero => simp [Pm_zero]
  | succ k ih =>
    rw [Pm_succ, ← Matrix.mulVec_mulVec, ih]
    by_cases hk : k < r + 1
    · rw [dif_pos hk, Matrix.mulVec_add, unitriangularColumnEichlerMatrix_initialVectors x hσ hJ hP]
      by_cases hck : c.val < k
      · have hne : c ≠ ⟨k, hk⟩ := fun h => by rw [h] at hck; exact lt_irrefl _ hck
        rw [if_pos hck, Mb_fix x hσ hJ hP _ _ (by rw [Fin.le_iff_val_le_val]; simp only [Fin.val_mk]; omega),
          if_pos (by omega : c.val < k + 1), if_neg hne, add_zero]
      · rw [if_neg hck, Matrix.mulVec_zero, add_zero]
        by_cases hce : c.val = k
        · have hc : c = ⟨k, hk⟩ := Fin.ext hce
          rw [if_pos hc, if_pos (by omega : c.val < k + 1), hc]
        · have hne : c ≠ ⟨k, hk⟩ := fun h => hce (by rw [h])
          rw [if_neg hne, if_neg (by omega : ¬ c.val < k + 1)]
    · have := c.isLt
      rw [dif_neg hk, Matrix.one_mulVec, if_pos (by omega : c.val < k), if_pos (by omega : c.val < k + 1)]

theorem Pm_unitary (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (hP : P.IsStd σ J T) (k : ℕ) :
    Formalism.UG.cT (sigR R σ) (Pm R σ J P T x k) * JR R J * Pm R σ J P T x k = JR R J := by
  induction k with
  | zero => simp [Pm_zero, Formalism.UG.cT_one]
  | succ k ih =>
    rw [Pm_succ]
    set M : Matrix (Fin n) (Fin n) (R ⊗[F] E) := if h : k < r + 1 then Mb R σ J P T x ⟨k, h⟩ else 1
    have hM : Formalism.UG.cT (sigR R σ) M * JR R J * M = JR R J := by
      simp only [M]
      split_ifs with hk
      · exact eich_unitary _ _ (sigR_invol R σ hσ) (fun i j => JR_herm R σ J hJ i j) _ _ _
          (yv_iso x hσ hJ hP _) (yv_w x hP _) (cc_cond hσ hJ hP _)
      · simp [Formalism.UG.cT_one]
    rw [Formalism.UG.cT_mul]
    calc Formalism.UG.cT (sigR R σ) (Pm R σ J P T x k) * Formalism.UG.cT (sigR R σ) M * JR R J * (M * Pm R σ J P T x k)
        = Formalism.UG.cT (sigR R σ) (Pm R σ J P T x k) * (Formalism.UG.cT (sigR R σ) M * JR R J * M) *
            Pm R σ J P T x k := by simp only [Matrix.mul_assoc]
      _ = JR R J := by rw [hM, ih]

end Product

section Units

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem JR_det_isUnit (hJ : IsHermND σ J) : IsUnit (JR (F := F) R J).det := by
  have h : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [JR, RingHom.map_det]
    rfl
  rw [h]
  exact (isUnit_iff_ne_zero.2 hJ.2).map _

variable {R σ J}

theorem inv_mul_of_unitary (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) :
    (JR (F := F) R J)⁻¹ * Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT (sigR R σ) M), hM,
    Matrix.nonsing_inv_mul _ hdet]

def uOf (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) : GL (Fin n) (R ⊗[F] E) where
  val := M
  inv := (JR (F := F) R J)⁻¹ * Formalism.UG.cT (sigR R σ) M * JR (F := F) R J
  val_inv := mul_eq_one_comm.1 (inv_mul_of_unitary hdet M hM)
  inv_val := inv_mul_of_unitary hdet M hM

def mkHA (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) : HA R σ J :=
  (⟨uOf hdet M hM, hM⟩ : HR R σ J)

theorem lin_mkHA (hdet : IsUnit (JR (F := F) R J).det) (M : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (hM : Formalism.UG.cT (sigR R σ) M * JR (F := F) R J * M = JR (F := F) R J) (w : Fin n → R ⊗[F] E) :
    lin R σ J (mkHA hdet M hM) w = M *ᵥ w := rfl

end Units

theorem unitri_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Continuous t ∧ (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP
  have hσ : ∀ e, σ (σ e) = e := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro e
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have hs : Continuous (sigR (Fv F v) σ) := by
    let L := LinearMap.baseChange (Fv F v) (σ.toLinearMap)
    have hL : ∀ a, sigR (Fv F v) σ a = L a := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, L]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have hc : Continuous L := IsModuleTopology.continuous_of_linearMap L
    exact hc.congr fun a => (hL a).symm
  have hdet := JR_det_isUnit (Fv F v) σ J hJ
  have hy : ∀ b, Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
      yv (Fv F v) P x b := by
    intro b
    refine continuous_finset_sum _ fun a _ => ?_
    have hc : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        coef (Fv F v) x b a := by
      by_cases h : a < b
      · simp only [coef, dif_pos h]
        exact continuous_apply _
      · simp only [coef, dif_neg h]
        exact continuous_const
    exact hc.smul continuous_const
  have hMb : ∀ b, Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
      Mb (Fv F v) σ J P T x b := by
    intro b
    have hsy : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        (sigR (Fv F v) σ ∘ yv (Fv F v) P x b) :=
      continuous_pi fun i => hs.comp ((continuous_apply i).comp (hy b))
    have hrow : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b) :=
      hsy.matrix_vecMul continuous_const
    have hrow2 : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        cc (E := E) (Fv F v) T b • row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b) -
          row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (wv (Fv F v) P T b) :=
      Continuous.sub (hrow.const_smul (cc (E := E) (Fv F v) T b)) (continuous_const (y := row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (wv (Fv F v) P T b)))
    have h1 : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        Matrix.vecMulVec (wv (Fv F v) P T b) (row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b)) :=
      continuous_const.matrix_vecMulVec hrow
    have h2 : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        Matrix.vecMulVec (yv (Fv F v) P x b) (cc (E := E) (Fv F v) T b • row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (yv (Fv F v) P x b) -
          row (sigR (Fv F v) σ) (JR (F := F) (Fv F v) J) (wv (Fv F v) P T b)) :=
      (hy b).matrix_vecMulVec hrow2
    exact (continuous_const.add h1).add h2
  have hPm : ∀ k, Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
      Pm (Fv F v) σ J P T x k := by
    intro k
    induction k with
    | zero => simp only [Pm_zero]; exact continuous_const
    | succ k ih =>
      simp only [Pm_succ]
      by_cases hk : k < r + 1
      · simp only [dif_pos hk]
        exact (hMb _).matrix_mul ih
      · simp only [dif_neg hk]
        exact continuous_const.matrix_mul ih
  refine ⟨fun x => mkHA hdet (Pm (Fv F v) σ J P T x (r + 1)) (Pm_unitary x hσ hJ hP (r + 1)), ?_, ?_⟩
  · have hinv : Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E =>
        (JR (F := F) (Fv F v) J)⁻¹ * Formalism.UG.cT (sigR (Fv F v) σ) (Pm (Fv F v) σ J P T x (r + 1)) * JR (F := F) (Fv F v) J := by
      simp only [Formalism.UG.cT]
      exact (continuous_const.matrix_mul ((hPm _).matrix_map hs).matrix_transpose).matrix_mul
        continuous_const
    exact Continuous.subtype_mk (p := fun g => g ∈ HR (Fv F v) σ J)
      (Units.continuous_iff.2 ⟨hPm (r + 1), hinv⟩) _
  · intro x b
    rw [lin_mkHA, unitriangularEichlerPartialProduct_initialVectors x hσ hJ hP, if_pos b.isLt]
    have hco : ∀ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 :
        Fv F v ⊗[F] E) = (if a = b then 1 else 0) + coef (Fv F v) x b a := by
      intro a
      by_cases hab : a = b
      · subst hab; simp [coef]
      · simp [hab, coef]
    simp only [hco, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

end GlobalTheory.UnitriSection
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitriangular_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Continuous t ∧ (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) := by
  atlas_forward_decl GlobalTheory.UnitriSection.unitri_section
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.HaarSectionProd

def prodHomeo {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace U]
    {S0 S : Subgroup G} (hS0S : S0 ≤ S) (t0 : U → G) (ht0c : Continuous t0) (ht0S : ∀ x, t0 x ∈ S)
    (ν : S → U) (hνc : Continuous ν)
    (hνt : ∀ s : S, ∀ s0 ∈ S0, ∀ x, (s : G) = s0 * t0 x → ν s = x)
    (hsec : ∀ s : S, (s : G) * (t0 (ν s))⁻¹ ∈ S0) : S0 × U ≃ₜ S where
  toFun p := ⟨p.1 * t0 p.2, S.mul_mem (hS0S p.1.2) (ht0S p.2)⟩
  invFun s := (⟨s * (t0 (ν s))⁻¹, hsec s⟩, ν s)
  left_inv p := by
    have h : ν ⟨p.1 * t0 p.2, S.mul_mem (hS0S p.1.2) (ht0S p.2)⟩ = p.2 :=
      hνt _ p.1 p.1.2 p.2 rfl
    ext
    · simp only [h, mul_inv_cancel_right]
    · simp only [h]
  right_inv s := by
    ext
    simp only [inv_mul_cancel_right]
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).mul (ht0c.comp continuous_snd)).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.mul ((ht0c.comp hνc).inv)).subtype_mk _).prodMk hνc

end GlobalTheory.HaarSectionProd

namespace GlobalTheory.HaarSectionProd

theorem haar_exists {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G]
    [TopologicalSpace U] [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
    {S0 S : Subgroup G} (hS0cl : IsClosed (S0 : Set G)) (hS0S : S0 ≤ S) (t0 : U → G)
    (ht0c : Continuous t0) (ht0S : ∀ x, t0 x ∈ S) (ν : S → U) (hνc : Continuous ν)
    (hνt : ∀ s : S, ∀ s0 ∈ S0, ∀ x, (s : G) = s0 * t0 x → ν s = x)
    (hsec : ∀ s : S, (s : G) * (t0 (ν s))⁻¹ ∈ S0)
    (μ0 : Measure S0) [μ0.IsHaarMeasure]
    (hconj : ∀ s ∈ S, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ h, f (s * (h : G) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : G) ∂μ0)
    (μU : Measure U) [SigmaFinite μU] [μU.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μU]
    (hshift : ∀ s ∈ S, ∃ φ : U → U, Measurable φ ∧ μU.map φ = μU ∧
      ∀ x, s * t0 x * (t0 (φ x))⁻¹ ∈ S0) :
    ∃ μS : Measure S, μS.IsHaarMeasure ∧ ∀ h : G → ℝ≥0∞, Measurable h → ∀ t : U → G,
      (∀ x, t x * (t0 x)⁻¹ ∈ S0) →
      ∫⁻ s, h s ∂(μS.map Subtype.val) = ∫⁻ x, ∫⁻ s0, h ((s0 : G) * t x) ∂μ0 ∂μU := by
  haveI : LocallyCompactSpace S0 := hS0cl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology S0 := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace S0 := inferInstance
  haveI : SigmaFinite μ0 := inferInstance
  set e := prodHomeo hS0S t0 ht0c ht0S ν hνc hνt hsec with he
  have he_m : Measurable e := e.continuous.measurable
  set μS : Measure S := (μ0.prod μU).map e with hμS
  have hright : ∀ c ∈ S0, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ s0, f ((s0 : G) * c) ∂μ0 = ∫⁻ s0, f (s0 : G) ∂μ0 := by
    intro c hc f hf
    have h1 := hconj c⁻¹ (S.inv_mem (hS0S hc)) (fun y => f (c * y)) (hf.comp (measurable_const_mul c))
    simp only [inv_inv, mul_assoc, mul_inv_cancel_left] at h1
    rw [h1]
    exact lintegral_mul_left_eq_self (fun h : S0 => f (h : G)) ⟨c, hc⟩
  have hkey : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ s, f s ∂(μS.map Subtype.val) = ∫⁻ x, ∫⁻ s0, f ((s0 : G) * t0 x) ∂μ0 ∂μU := by
    intro f hf
    have hfv : Measurable (fun k : S => f (k : G)) := hf.comp measurable_subtype_coe
    rw [lintegral_map hf measurable_subtype_coe, hμS, lintegral_map hfv he_m,
      lintegral_prod_symm (fun p => f (e p : G)) (hfv.comp he_m).aemeasurable]
    rfl
  have hleft : ∀ g ∈ S, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, ∫⁻ s0, f (g * ((s0 : G) * t0 x)) ∂μ0 ∂μU = ∫⁻ x, ∫⁻ s0, f ((s0 : G) * t0 x) ∂μ0 ∂μU := by
    intro g hg f hf
    obtain ⟨φ, hφm, hφ, hφS⟩ := hshift g hg
    have hGm : Measurable (fun y => ∫⁻ s0, f ((s0 : G) * t0 y) ∂μ0) := by
      have : Measurable (fun p : S0 × U => f ((p.1 : G) * t0 p.2)) :=
        hf.comp ((continuous_subtype_val.comp continuous_fst).mul (ht0c.comp continuous_snd)).measurable
      exact this.lintegral_prod_left'
    have hin : ∀ x, ∫⁻ s0, f (g * ((s0 : G) * t0 x)) ∂μ0 = ∫⁻ s0, f ((s0 : G) * t0 (φ x)) ∂μ0 := by
      intro x
      set c := g * t0 x * (t0 (φ x))⁻¹ with hcdef
      have hc : c ∈ S0 := hφS x
      have e1 : ∀ s0 : G, g * (s0 * t0 x) = g * s0 * g⁻¹ * (c * t0 (φ x)) := by
        intro s0; rw [hcdef]; group
      simp_rw [e1]
      have h2 := hconj g hg (fun y => f (y * (c * t0 (φ x)))) (hf.comp (measurable_mul_const _))
      rw [h2]
      have h3 := hright c hc (fun y => f (y * t0 (φ x))) (hf.comp (measurable_mul_const _))
      simpa only [mul_assoc] using h3
    simp_rw [hin]
    rw [← lintegral_map hGm hφm, hφ]
  have hinv : μS.IsMulLeftInvariant := by
    refine ⟨fun k0 => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_mul k0) hA]
    obtain ⟨B, hB, rfl⟩ := hA
    have hB' : MeasurableSet ((fun y : G => (k0 : G) * y) ⁻¹' B) := measurable_const_mul _ hB
    have e1 : μS ((fun k => k0 * k) ⁻¹' (Subtype.val ⁻¹' B)) =
        (μS.map Subtype.val) ((fun y : G => (k0 : G) * y) ⁻¹' B) := by
      rw [Measure.map_apply measurable_subtype_coe hB']; rfl
    have e2 : μS (Subtype.val ⁻¹' B) = (μS.map Subtype.val) B := by
      rw [Measure.map_apply measurable_subtype_coe hB]
    rw [e1, e2, ← lintegral_indicator_one hB', ← lintegral_indicator_one hB,
      hkey _ (measurable_one.indicator hB'), hkey _ (measurable_one.indicator hB)]
    have hz : ∀ z, ((fun y : G => (k0 : G) * y) ⁻¹' B).indicator (1 : G → ℝ≥0∞) z =
        B.indicator 1 ((k0 : G) * z) := fun z => by
      by_cases hz : (k0 : G) * z ∈ B <;> simp [Set.indicator, hz]
    simp_rw [hz]
    exact hleft k0 k0.2 _ (measurable_one.indicator hB)
  have hfin : IsFiniteMeasureOnCompacts μS := Measure.IsFiniteMeasureOnCompacts.map _ e
  have hopen : μS.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hHaar : μS.IsHaarMeasure := by
    haveI := hfin; haveI := hinv; haveI := hopen
    exact ⟨⟩
  refine ⟨μS, hHaar, ?_⟩
  intro h hh t ht
  rw [hkey h hh]
  congr 1
  funext x
  have h4 := hright _ (ht x) (fun y => h (y * t0 x)) (hh.comp (measurable_mul_const _))
  simp only [mul_assoc, inv_mul_cancel, mul_one] at h4
  exact h4.symm

end GlobalTheory.HaarSectionProd

namespace GlobalTheory.HaarSectionProd

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

def umat {K : Type} [Zero K] [One K] (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0

def UTri {K : Type} [Zero K] [One K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Prop :=
  (∀ i, A i i = 1) ∧ ∀ i j, j < i → A i j = 0

theorem umat_utri {K : Type} [Zero K] [One K] (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → K) :
    UTri (umat x) := by
  refine ⟨fun i => by simp [umat], fun i j h => ?_⟩
  simp [umat, h.ne', not_lt.mpr h.le]

theorem utri_mul {K : Type} [CommRing K] {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hA : UTri A) (hB : UTri B) : UTri (A * B) := by
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [hA.1, hB.1]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · simp [hA.2 _ _ h]
      · simp [hB.2 _ _ h]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : c < i
    · simp [hA.2 _ _ h]
    · simp [hB.2 _ _ (lt_of_lt_of_le hji (not_lt.mp h))]

theorem umat_of_utri {K : Type} [Zero K] [One K] {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hA : UTri A) : umat (fun p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} => A p.1.1 p.1.2) = A := by
  ext a b
  simp only [umat, Matrix.of_apply]
  split_ifs with h1 h2
  · subst h1; exact (hA.1 a).symm
  · rfl
  · exact (hA.2 a b (lt_of_le_of_ne (not_lt.mp h2) (fun e => h1 e.symm))).symm

variable (P : Frame E n r)

def Coef (g : HA R σ J) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) (R ⊗[F] E)) : Prop :=
  ∀ b, lin R σ J g (ratV (F := F) R (F0 P b)) = ∑ a, A a b • ratV (F := F) R (F0 P a)

variable {P}

theorem coef_mul {g k : HA R σ J} {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) (R ⊗[F] E)}
    (hg : Coef P g A) (hk : Coef P k B) : Coef P (g * k) (A * B) := by
  have hg' : ∀ a, lin R σ J g (ratV (F := F) R (F0 P a)) = ∑ c, A c a • ratV (F := F) R (F0 P c) := hg
  intro b
  rw [lin_mul, hk b, map_sum]
  simp only [map_smul, hg', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem coef_one_of_mem {g : HA R σ J} (hg : g ∈ S0 R σ J P) : Coef P g 1 := by
  intro b
  rw [(mem_stabT R σ J (F0 P) g).1 hg b]
  simp [Matrix.one_apply]

theorem frameFixerSubgroup_le_frameStabilizerSubgroup : S0 R σ J P ≤ Ssub R σ J P := by
  intro g hg
  show UniC R σ J (F0 P) g
  intro b
  rw [(mem_stabT R σ J (F0 P) g).1 hg b, sub_self]
  exact Submodule.zero_mem _

theorem mem_Ssub_of_coef {g : HA R σ J} {x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → R ⊗[F] E}
    (hg : Coef P g (umat x)) : g ∈ Ssub R σ J P := by
  show UniC R σ J (F0 P) g
  intro b
  rw [hg b]
  have hb : ratV (F := F) R (F0 P b) = ∑ a, (if a = b then ratV (F := F) R (F0 P a) else 0) := by
    simp
  rw [hb, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun a _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp only [umat, Matrix.of_apply, h.ne, if_false, dif_pos h, sub_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, rfl⟩)
  · subst h; simp [umat]
  · simp [umat, h.ne', not_lt.mpr h.le]

theorem mul_inv_mem_frameFixer_of_agree_on_frame {g k : HA R σ J} (hk : k ∈ Ssub R σ J P)
    (h : ∀ b, lin R σ J g (ratV (F := F) R (F0 P b)) = lin R σ J k (ratV (F := F) R (F0 P b))) :
    g * k⁻¹ ∈ S0 R σ J P := by
  show g * k⁻¹ ∈ stabT R σ J (F0 P)
  rw [mem_stabT]
  have hgw : ∀ w ∈ spanR (F := F) R (F0 P) Set.univ, lin R σ J g w = lin R σ J k w := by
    intro w hw
    unfold spanR at hw
    induction hw using Submodule.span_induction with
    | mem y hy => obtain ⟨a, _, rfl⟩ := hy; exact h a
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, map_smul, hx]
  intro b
  obtain ⟨w, hw, hwk⟩ := uni_le_map (Y := F0 P) (g := k) hk Set.univ (fun _ _ _ _ => Set.mem_univ _)
    (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)
  have hwk' : lin R σ J k w = ratV (F := F) R (F0 P b) := hwk
  rw [lin_mul, ← hwk', lin_inv_lin, hgw w hw]

theorem coef_agree {g k : HA R σ J} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) (R ⊗[F] E)}
    (hg : Coef P g A) (hk : Coef P k A) (hkS : k ∈ Ssub R σ J P) : g * k⁻¹ ∈ S0 R σ J P :=
  mul_inv_mem_frameFixer_of_agree_on_frame hkS fun b => by rw [hg b, hk b]

end Alg

end GlobalTheory.HaarSectionProd

namespace GlobalTheory.HaarSectionProd

theorem umat_entry_continuous {K : Type} [TopologicalSpace K] [Zero K] [One K] {r : ℕ} (a b : Fin (r + 1)) :
    Continuous fun x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → K => umat x a b := by
  simp only [umat, Matrix.of_apply]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const

theorem haar_S_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP μ0 hμ0 hconj μU hμU
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, -⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i6; haveI := i7; haveI := i8
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨t0, ht0c, ht0⟩ := GlobalTheory.T.exists_continuous_unitriangular_section F E σ hCM n J hJ v r P T hP
  obtain ⟨ν, hνc, hν⟩ := GlobalTheory.UnitriangularCoeff.exists_coeff F E σ hCM n J hJ v r P T hP
  have ht0coef : ∀ x, Coef P (t0 x) (umat x) := ht0
  have hνcoef : ∀ s : Ssub (Fv F v) σ J P, Coef P (s : HA (Fv F v) σ J) (umat (ν s)) :=
    fun s => (hν s (ν s)).1 rfl
  have ht0S : ∀ x, t0 x ∈ Ssub (Fv F v) σ J P := fun x => mem_Ssub_of_coef (ht0coef x)
  have hS0cl : IsClosed (S0 (Fv F v) σ J P : Set (HA (Fv F v) σ J)) :=
    PI.VolSemiDirect.W.isClosed_stabT (Fv F v) σ J (F0 P)
  have hνt : ∀ s : Ssub (Fv F v) σ J P, ∀ s0 ∈ S0 (Fv F v) σ J P, ∀ x,
      (s : HA (Fv F v) σ J) = s0 * t0 x → ν s = x := by
    intro s s0 hs0 x hs
    have hc : Coef P (s : HA (Fv F v) σ J) (umat x) := by
      rw [hs]
      have := coef_mul (coef_one_of_mem hs0) (ht0coef x)
      rwa [Matrix.one_mul] at this
    exact ((hν s x).2 hc).symm
  have hsec : ∀ s : Ssub (Fv F v) σ J P, (s : HA (Fv F v) σ J) * (t0 (ν s))⁻¹ ∈ S0 (Fv F v) σ J P :=
    fun s => coef_agree (hνcoef s) (ht0coef (ν s)) (ht0S _)
  have hshift : ∀ s ∈ Ssub (Fv F v) σ J P, ∃ φ : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) →
      ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), Measurable φ ∧ μU.map φ = μU ∧
      ∀ x, s * t0 x * (t0 (φ x))⁻¹ ∈ S0 (Fv F v) σ J P := by
    intro s hs
    set u := umat (ν ⟨s, hs⟩) with hu
    have hφc : Continuous (fun (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E)
        (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}) => (u * umat x) p.1.1 p.1.2) := by
      refine continuous_pi fun p => ?_
      simp only [Matrix.mul_apply]
      exact continuous_finset_sum _ fun c _ => continuous_const.mul (umat_entry_continuous c p.1.2)
    refine ⟨_, hφc.measurable, GlobalTheory.UnitriHaar.map_unitri_mul F E v r μU hμU u (umat_utri _).1 (umat_utri _).2, ?_⟩
    intro x
    have h1 : Coef P (s * t0 x) (u * umat x) := coef_mul (hνcoef ⟨s, hs⟩) (ht0coef x)
    rw [← umat_of_utri (utri_mul (umat_utri (ν ⟨s, hs⟩)) (umat_utri x))] at h1
    exact coef_agree h1 (ht0coef _) (ht0S _)
  obtain ⟨μS, hH, hF⟩ := haar_exists hS0cl frameFixerSubgroup_le_frameStabilizerSubgroup t0 ht0c ht0S ν hνc hνt hsec μ0 hconj μU hshift
  exact ⟨μS, hH, fun h hh t ht => hF h hh t fun x => coef_agree (ht x) (ht0coef x) (ht0S x)⟩

end GlobalTheory.HaarSectionProd
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  atlas_forward_decl GlobalTheory.HaarSectionProd.haar_S_local
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

namespace GlobalTheory.TraceSelfDual

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [Field R] [Algebra F R]
  (ι : Type) [Fintype ι]

noncomputable def traceBilin : LinearMap.BilinForm R (ι → R ⊗[F] E) :=
  LinearMap.mk₂ R (fun x y => ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem traceBilin_apply (x y : ι → R ⊗[F] E) :
    traceBilin R ι x y = ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i) := rfl

theorem traceBilin_symm (x y : ι → R ⊗[F] E) : traceBilin R ι x y = traceBilin R ι y x := by
  simp only [traceBilin_apply, mul_comm]

variable [NumberField F] [NumberField E]

theorem eq_zero_of_traceBilin {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : ι → R ⊗[F] E)
    (hx : ∀ y, traceBilin R ι x y = 0) : x = 0 := by
  classical
  funext j
  refine GlobalTheory.SelfDualFinite.eq_zero_of_trace R h _ fun c => ?_
  have := hx (Pi.single j c)
  rw [traceBilin_apply, Finset.sum_eq_single j] at this
  · rwa [Pi.single_eq_same, mul_comm] at this
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form

theorem exists_selfDual_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), (∃ r, psiV F ψ v r ≠ 1) → ∀ (ι : Type) [Fintype ι], ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))) := by
  intro F E _ _ _ _ _ σ h ψ hψ v hne ι _
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  exact (GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne _ (traceBilin (Fv F v) ι)
    (traceBilin_symm _ ι) (eq_zero_of_traceBilin _ ι h)).exists

end GlobalTheory.TraceSelfDual
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserTie

theorem exists_tied_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  intro F E _ _ _ _ _ σ hcm n J hJ hW hC ψ hψ hstd v r P T hP hn μG hG
  obtain ⟨-, -, hT, -, -⟩ := GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP
  obtain ⟨hdX, hdT, hOm⟩ := GlobalTheory.T.localSelfDualMeasures_fibreFamily_exist F E σ hcm n J hJ hW hC ψ hψ v (r + 1) (by omega) hn
  have hfib : IsFibreFamily (Formalism.L2.SG.LocVol.dX σ J ψ v (r + 1)) (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} (Formalism.L2.SG.LocVol.dT σ ψ v (r + 1)) Set.univ
      (Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1)) := hOm
  obtain ⟨μ0, hμ0, hc1, hc2⟩ := GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μG hG
  have hconj := GlobalTheory.T.similitude_conj_preserves_unitary_haar_at_finite_place F E σ hcm n J hJ v r P T hP hT _ _ hdX hdT _ hfib μ0 hμ0
  have hne : ∃ x, psiV F ψ v x ≠ 1 := GlobalTheory.StdCharTotReal.exists_psiV_ne_one F hcm.1 ψ hψ hstd v
  have hsd := GlobalTheory.TraceSelfDual.exists_selfDual_trace F E σ hcm ψ hψ v hne (Formalism.L2.SG.LocVol.UIdx r)
  have hU : (Formalism.L2.SG.LocVol.sdE (E := E) ψ v (Formalism.L2.SG.LocVol.UIdx r)).IsAddHaarMeasure := by
    unfold Formalism.L2.SG.LocVol.sdE
    rw [dif_pos hsd]
    exact hsd.choose_spec.1
  obtain ⟨μS, hμS, hprod⟩ := GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product F E σ hcm n J hJ v r P T hP μ0 hμ0 hconj _ hU
  refine ⟨μS, hμS, μ0, hμ0, ?_, ?_⟩
  · have hom : Formalism.L2.SG.LocVol.omAt σ J ψ v (Formalism.L2.SG.LocVol.TFl σ J v P)
        = Formalism.L2.SG.LocVol.omFam σ J ψ v (r + 1) (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT) := by
      unfold Formalism.L2.SG.LocVol.omAt
      have hmem : Formalism.L2.SG.LocVol.TFl σ J v P ∈ HermR (Fv F v) σ (r + 1) :=
        map_mem_HermR (Fv F v) σ _ hT
      rw [dif_pos hmem]
      rfl
    unfold Formalism.L2.SG.LocVol.IsCompatLoc
    rw [hom]
    exact ⟨hc1, hc2⟩
  · intro h hh t ht
    exact hprod h hh t ht

end GlobalTheory.LocalStabiliserTie
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → Formalism.L2.SG.LocVol.IsStdChar ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → 2 * (r + 1) < n → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW σ J ψ v P μG μS := by
  atlas_forward_decl GlobalTheory.LocalStabiliserTie.exists_tied_haar
end

section
noncomputable section

namespace GlobalTheory.UnipFlagCore

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Matrix
open scoped TensorProduct ENNReal

theorem mem_spanR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n r : ℕ}
    (e : Fin r → Fin n → E) (s : Set (Fin r)) (w : Fin n → R ⊗[F] E) :
    w ∈ spanR (F := F) R e s ↔
      ∃ c : Fin r → R ⊗[F] E, (∀ b, b ∉ s → c b = 0) ∧ w = ∑ b, c b • ratTup (F := F) R e b := by
  classical
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨Pi.single a 1, fun b hb => ?_, ?_⟩
      · exact Pi.single_eq_of_ne (by rintro rfl; exact hb ha) _
      · rw [Finset.sum_eq_single a]
        · simp only [Pi.single_eq_same, one_smul]; rfl
        · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
        · simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨t • c, fun b hb => by simp [hc b hb], ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hc b hb, zero_smul]; exact Submodule.zero_mem _

theorem hE_swap {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) : hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ.1 j i]; ring

theorem nsub_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F),
    P.IsStd σ J T → ∃ K : Set (Nsub (AF F) σ J P), IsCompact K ∧
      ∀ m : Nsub (AF F) σ J P, ∃ γ ∈ ratOf (K := Nsub (AF F) σ J P), ∃ k ∈ K, m = γ * k := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hσ := conj_invol hCM
  obtain ⟨h0, -, hef, -, -, -, -⟩ := hP
  have he : LinearIndependent E P.e := linearIndependent_of_dual P.e P.f fun a b => by
    rw [hE_swap hσ hJ (P.e b) (P.f a), hef]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hlin : ∀ (g : HA (AF F) σ J) (x : Fin n → AF F ⊗[F] E),
      lin (AF F) σ J g x - x = ((HA.mat _ σ J g).1 - 1) *ᵥ x := fun g x => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  obtain ⟨K, hK, hm⟩ := cocompact_of_mem_iff_adelic hσ hJ P.e he h0 (Nsub (AF F) σ J P) fun g => by
    refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun x => imp_congr Iff.rfl ?_)
    · have := mem_spanR_iff (F := F) (AF F) P.e {b | b < a} (lin (AF F) σ J g (ratV (F := F) (AF F) (P.e a)) - ratV (F := F) (AF F) (P.e a))
      rw [this, hlin]
      simp only [Set.mem_setOf_eq, not_lt]
      rfl
    · have := mem_spanR_iff (F := F) (AF F) P.e Set.univ (lin (AF F) σ J g x - x)
      rw [this, hlin]
      simp only [Set.mem_univ, not_true_eq_false, false_imp_iff, implies_true, true_and]
  refine ⟨K, hK, fun m => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hm m
  exact ⟨γ, hγ, k, hk, rfl⟩

end GlobalTheory.UnipFlagCore
end
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

section General

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] (Γ : Subgroup K) (μ : Measure K)

theorem measure_eq [Countable Γ] [μ.IsMulLeftInvariant] {s t : Set K}
    (hs : IsFundamentalDomain Γ s μ) (ht : IsFundamentalDomain Γ t μ) : μ s = μ t := hs.measure_eq ht

omit [IsTopologicalGroup K] [BorelSpace K] in

theorem measure_ne_zero [Countable Γ] [μ.IsHaarMeasure] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) : μ s ≠ 0 :=
  hs.measure_ne_zero (NeZero.ne μ)

theorem measure_le_of_cover [Countable Γ] [μ.IsMulLeftInvariant] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) {C : Set K}
    (hcov : ∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) : μ s ≤ μ C := by
  open Pointwise in
  calc μ s ≤ μ (⋃ g : Γ, g • toMeasurable μ C ∩ s) := by
          refine measure_mono fun m hm => ?_
          obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov m
          refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_, hm⟩
          exact ⟨k, subset_toMeasurable μ C hk, rfl⟩
      _ ≤ ∑' g : Γ, μ (g • toMeasurable μ C ∩ s) := measure_iUnion_le _
      _ = μ (toMeasurable μ C) := (hs.measure_eq_tsum _).symm
      _ = μ C := measure_toMeasurable C

omit [TopologicalSpace K] [IsTopologicalGroup K] [BorelSpace K] in

theorem isFundamentalDomain_smul_iff {c : NNReal} (hc : c ≠ 0) (s : Set K) :
    IsFundamentalDomain Γ s (c • μ) ↔ IsFundamentalDomain Γ s μ := by
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro h
    refine h.mono fun t ht => ?_
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left hc'
  · intro h
    refine h.mono fun t ht => ?_
    rw [Measure.smul_apply, ht, smul_zero]

private theorem exists_measurableSet_unique_smul_mem_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V)
    (hΓV : ∀ γ ∈ Γ, γ ∈ V → γ = 1) :
    ∃ s : Set G, MeasurableSet s ∧ ∀ x : G, ∃! g : Γ, g • x ∈ s := by
  classical

  obtain ⟨U, hUo, hU1, hUV⟩ := exists_open_nhds_one_split (hV.mem_nhds h1)
  let W : Set G := U ∩ (fun u => u⁻¹) ⁻¹' U
  have hWo : IsOpen W := hUo.inter (hUo.preimage continuous_inv)
  have hW1 : (1 : G) ∈ W := ⟨hU1, by simp only [Set.mem_preimage, inv_one]; exact hU1⟩
  have hWW : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ V := fun a ha b hb => hUV a ha.1 b⁻¹ hb.2

  let A : G → Set G := fun g => (fun x => x * g⁻¹) ⁻¹' W
  have hAo : ∀ g, IsOpen (A g) := fun g => hWo.preimage (continuous_mul_const _)
  have hcov : ⋃ g, A g = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.2 ⟨x, by simp only [A, Set.mem_preimage, mul_inv_cancel]; exact hW1⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable A hAo
  have hmemT : ∀ x, ∃ g ∈ T, x ∈ A g := fun x => by
    have hx : x ∈ ⋃ g ∈ T, A g := by rw [hTU, hcov]; exact Set.mem_univ x
    obtain ⟨g, hg, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨g, hg, hx'⟩
  have hTne : T.Nonempty := by
    obtain ⟨g, hg, -⟩ := hmemT 1
    exact ⟨g, hg⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set G := fun i => A (f i)
  have hBo : ∀ i, IsOpen (B i) := fun i => hAo _
  have hBcov : ∀ x, ∃ i, x ∈ B i := by
    intro x
    obtain ⟨g, hgT, hx⟩ := hmemT x
    rw [hf] at hgT
    obtain ⟨i, rfl⟩ := hgT
    exact ⟨i, hx⟩

  have hinj : ∀ i y (δ : Γ), y ∈ B i → δ • y ∈ B i → δ = 1 := by
    intro i y δ hy hδy
    have hm := hWW (δ • y * (f i)⁻¹) hδy (y * (f i)⁻¹) hy
    have he : δ • y * (f i)⁻¹ * (y * (f i)⁻¹)⁻¹ = (δ : G) := by
      simp only [Subgroup.smul_def, smul_eq_mul]
      group
    rw [he] at hm
    exact Subtype.ext (hΓV _ δ.2 hm)

  let E : ℕ → Set G := fun j => ⋃ γ : Γ, (fun x => γ • x) ⁻¹' B j
  have hEo : ∀ j, IsOpen (E j) := fun j => isOpen_iUnion fun γ => (hBo j).preimage
    (by simpa only [Subgroup.smul_def, smul_eq_mul] using continuous_const_mul (γ : G))
  have hE : ∀ j y, y ∈ E j ↔ ∃ δ : Γ, δ • y ∈ B j := fun j y => by
    simp only [E, Set.mem_iUnion, Set.mem_preimage]

  let s : Set G := ⋃ i, (B i \ ⋃ (j : ℕ) (_ : j < i), E j)
  have hs : ∀ y, y ∈ s ↔ ∃ i, y ∈ B i ∧ ∀ j < i, ∀ δ : Γ, δ • y ∉ B j := by
    intro y
    simp only [s, Set.mem_iUnion, Set.mem_sdiff, not_exists]
    constructor
    · rintro ⟨i, hi, hn⟩
      exact ⟨i, hi, fun j hj δ hδ => hn j hj ((hE j y).2 ⟨δ, hδ⟩)⟩
    · rintro ⟨i, hi, hn⟩
      refine ⟨i, hi, fun j hj hy => ?_⟩
      obtain ⟨δ, hδ⟩ := (hE j y).1 hy
      exact hn j hj δ hδ
  refine ⟨s, MeasurableSet.iUnion fun i => (hBo i).measurableSet.diff
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hEo j).measurableSet, fun x => ?_⟩
  have hP : ∃ i, ∃ γ : Γ, γ • x ∈ B i := by
    obtain ⟨i, hi⟩ := hBcov x
    exact ⟨i, 1, by simpa only [one_smul] using hi⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  refine ⟨γ, (hs _).2 ⟨_, hγ, fun j hj δ hδ => Nat.find_min hP hj ⟨δ * γ, by rwa [mul_smul]⟩⟩,
    fun γ' hγ' => ?_⟩
  obtain ⟨i', hi', hmin'⟩ := (hs _).1 hγ'
  have hle : Nat.find hP ≤ i' := Nat.find_min' hP ⟨γ', hi'⟩
  have hge : i' ≤ Nat.find hP := by
    by_contra hlt
    exact hmin' _ (not_le.1 hlt) (γ * γ'⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hγ)
  rw [le_antisymm hge hle] at hi'
  have h1' := hinj _ (γ • x) (γ' * γ⁻¹) hγ (by rw [mul_smul, inv_smul_smul]; exact hi')
  exact mul_inv_eq_one.1 h1'

end General

theorem countable_and_exists_domain (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) :
    IsTopologicalGroup K ∧ BorelSpace K ∧
    Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) ∧
    ∀ μ : Measure K, ∃ 𝓕 : Set K,
      IsFundamentalDomain (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) 𝓕 μ := by
  obtain ⟨hc, hd, -⟩ := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ n J
  change Countable (HFinIn (AF F) σ J) at hc
  change DiscreteTopology (HFinIn (AF F) σ J) at hd

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set (HFinIn (AF F) σ J)))
  have ht1 : (1 : HA (AF F) σ J) ∈ t := by
    have h : (1 : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := by rw [hteq]; exact Set.mem_singleton _
    exact h
  have htone : ∀ h ∈ HFinIn (AF F) σ J, h ∈ t → h = 1 := by
    intro h hh hht
    have h' : (⟨h, hh⟩ : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := hht
    rw [hteq] at h'
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h')
  have hcnt : Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) := by
    refine Function.Injective.countable
      (f := fun x => (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_subgroupOf.1 x.2⟩ :
        HFinIn (AF F) σ J)) ?_
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)

  have : SecondCountableTopology (AF F) := AdelicUnitaryTop.secondCountable_adele F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' (AF F) (AF F ⊗[F] E)
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hφ
  have : SecondCountableTopology (AF F ⊗[F] E) :=
    hq.isQuotientMap.secondCountableTopology hq.isOpenMap
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AF F ⊗[F] E)) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (HA (AF F) σ J) :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : HR (AF F) σ J → GL (Fin n) (AF F ⊗[F] E))).secondCountableTopology
  have : IsTopologicalGroup (HA (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  refine ⟨inferInstance, inferInstance, hcnt, fun μ => ?_⟩
  have hK1 : IsTopologicalGroup K := inferInstance
  have hK2 : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hK3 : OpensMeasurableSpace K := inferInstance
  obtain ⟨s, hs, hex⟩ := @exists_measurableSet_unique_smul_mem_of_discrete K _ _ hK1 hK2 _ hK3
    (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    ((Subtype.val : K → HA (AF F) σ J) ⁻¹' t) (ht.preimage continuous_subtype_val) ht1
    (fun γ hγ hγV => Subtype.ext (htone _ (Subgroup.mem_subgroupOf.1 hγ) hγV))
  exact ⟨s, IsFundamentalDomain.mk' hs.nullMeasurableSet hex⟩

theorem domains_and_covolume (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) (Γ : Subgroup K)
    (hΓ : Γ = Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    (cov : Measure K → ℝ)
    (hcov : ∀ ν : Measure K, (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν) →
      ∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν ∧ cov ν = (ν 𝓕).toReal)
    (μ : Measure K) (hμ : μ.IsHaarMeasure) :
    (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ) ∧
    (∀ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ → cov μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧
      ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧
    ∀ c : NNReal, c ≠ 0 → cov (c • μ) = (c : ℝ) * cov μ := by
  obtain ⟨hTG, hB, hcnt, hex⟩ := countable_and_exists_domain F E σ n J K
  rw [← hΓ] at hcnt hex
  have := hμ
  refine ⟨hex μ, fun 𝓕 h𝓕 => ?_, fun c hc => ?_⟩
  · obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    refine ⟨?_, @GlobalTheory.ClosedSubgroupCovol.measure_ne_zero _ _ _ _ Γ μ hcnt _ _ h𝓕,
      fun C _ hC => @GlobalTheory.ClosedSubgroupCovol.measure_le_of_cover _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕 _ hC⟩
    rw [hcv, @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓕' h𝓕]
  · obtain ⟨𝓕, h𝓕⟩ := hex μ
    obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    obtain ⟨𝓖, h𝓖, hcv'⟩ := hcov (c • μ) ⟨𝓕, (isFundamentalDomain_smul_iff Γ μ hc 𝓕).2 h𝓕⟩
    have h𝓖μ := (isFundamentalDomain_smul_iff Γ μ hc 𝓖).1 h𝓖
    rw [hcv', hcv, Measure.smul_apply,
      @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓖μ h𝓕', ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory.ClosedSubgroupCovol
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

theorem fundamentalDomain_covol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ K : Subgroup (HA (AF F) σ J), IsClosed (K : Set (HA (AF F) σ J)) → ∀ μ : Measure K, μ.IsHaarMeasure → (∃ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) ∧ (∀ 𝓕 : Set K, IsFundamentalDomain (ratOf (K := K)) 𝓕 μ → covol μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧ ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ ratOf (K := K), ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧ ∀ c : NNReal, c ≠ 0 → covol (c • μ) = (c : ℝ) * covol μ := by
  intro F E _ _ _ _ _ σ _ n J _ K _ μ hμ

  refine domains_and_covolume F E σ n J K (ratOf (K := K)) rfl covol ?_ μ hμ
  intro ν hν
  refine ⟨hν.choose, hν.choose_spec, ?_⟩
  rw [covol, dif_pos hν]

end GlobalTheory.ClosedSubgroupCovol
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.NsubHaarCovol

theorem exists_haar_covol_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hcl : IsClosed (Nsub (AF F) σ J P : Set (HA (AF F) σ J)) :=
    PI.UnitaryGroupMassFormula.MeasWCore.isClosed_Nsub (AF F) σ J P
  let μ0 : Measure (Nsub (AF F) σ J P) := Measure.haar
  have hμ0 : μ0.IsHaarMeasure := inferInstance
  obtain ⟨⟨𝓕, h𝓕⟩, hall, hscale⟩ :=
    GlobalTheory.ClosedSubgroupCovol.fundamentalDomain_covol F E σ hCM n J hJ _ hcl μ0 hμ0
  obtain ⟨Kc, hKc, hcov⟩ := GlobalTheory.UnipFlagCore.nsub_cocompact F E σ hCM n J hJ r P T hP
  obtain ⟨hcv, hne, hle⟩ := hall 𝓕 h𝓕
  have hfin : μ0 𝓕 ≠ ∞ :=
    ((hle Kc hKc.isClosed.measurableSet hcov).trans_lt hKc.measure_lt_top).ne
  have hpos : 0 < (μ0 𝓕).toReal := ENNReal.toReal_pos hne hfin
  have hc0 : ((μ0 𝓕).toNNReal)⁻¹ ≠ 0 := inv_ne_zero (by
    intro h; rw [ENNReal.toNNReal_eq_zero_iff] at h; exact h.elim hne hfin)
  refine ⟨((μ0 𝓕).toNNReal)⁻¹ • μ0, Measure.IsHaarMeasure.nnreal_smul _ hc0, ?_⟩
  rw [hscale _ hc0, hcv, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
  exact inv_mul_cancel₀ hpos.ne'

end GlobalTheory.NsubHaarCovol
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  atlas_forward_decl GlobalTheory.NsubHaarCovol.exists_haar_covol_one
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.Rescale

theorem rescaleStep3 :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.St.RescaleStep3 D := by
  intro hSW D X hb hM
  obtain ⟨hCM, hH, hsize, hfr⟩ := GlobalTheory.CmHermitianRankFrames.cm_herm_rank_frames D X
  obtain ⟨hA, hC⟩ := GlobalTheory.St.siegelWeil_volumes hSW X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
  obtain ⟨ψ, hψ, hstd⟩ := Formalism.L2.SG.Pf.standard_character_exists X.B.I.F hCM.1
  have hstd' : Formalism.L2.SG.LocVol.IsStdChar ψ := hstd
  have hG := X.measG_norm
  have hμG : X.measG.μG.IsHaarMeasure := hG.1
  have hherm : ∀ {a : ℕ} (X0 : Fin a → Fin X.B.I.n → X.B.I.E) (i j : Fin a),
      X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j :=
    fun X0 i j => GlobalTheory.FrameGram.hE_swap (GlobalTheory.FrameGram.conj_invol hCM) hH.1 _ _

  have hB : ∀ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E,
      ∃ μ' : Measure (stabT (AF X.B.I.F) X.B.I.cm.sig X.B.I.J X0), μ'.IsHaarMeasure ∧
        ((gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
          ∃ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) =
              gramE X.B.I.cm.sig X.B.I.J X0 i j) (νB : Measure _),
            Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB ∧
            Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG μ' νB) := by
    intro X0
    by_cases hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0
    · obtain ⟨νX, μ', h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
        (2 * D.R.rS + 2) (by omega) (by omega) X0 (hherm X0) hdet X.measG.μG hμG
      exact ⟨μ', h2, fun _ => ⟨hherm X0, νX, h1, h3⟩⟩
    · exact ⟨X.measG.μB X0, hG.2.2.2.2.1 X0, fun h => absurd h hdet⟩
  choose μB' hμB' hBc using hB

  have hW : ∀ u, ∃ W : MeasW X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u), W.IsTextNorm ∧
      W.μNinf = (X.measW u).μNinf ∧ W.μHinf = (X.measW u).μHinf ∧
      (∃ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) j i) =
            gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) i j) (νH : Measure _),
        Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH ∧
        Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J
          (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) X.measG.μG W.μH νH) ∧
      covol W.μN = 1 ∧
      ∀ v, Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v (Formalism.L2.SG.TypedSets.frameOf X u)
        (X.measG.μGv v) (W.μSv v) := by
    intro u
    obtain ⟨T, hP⟩ := hfr u
    obtain ⟨hdet, hT1, -⟩ := GlobalTheory.FrameGram.std_frame_gram X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
      D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    obtain ⟨νH, μH, h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
      (D.R.rS + 1 + D.R.rS) (by omega) (by omega) (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) hT1 hdet
      X.measG.μG hμG
    obtain ⟨μN, hN, hN1⟩ := GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH D.R.rS
      (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    have hS : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
        ∃ μS : Measure (Ssub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u)),
          μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v
            (Formalism.L2.SG.TypedSets.frameOf X u) (X.measG.μGv v) μS := fun v =>
      GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ hstd' v D.R.rS
        (Formalism.L2.SG.TypedSets.frameOf X u) T hP (by omega) (X.measG.μGv v) (hG.2.2.2.1 v)
    choose μSv hSv hSt using hS
    have hWn := X.measW_norm u
    obtain ⟨W, hWt, e1, e2, e3, e4, e5⟩ := GlobalTheory.St.MeasWord.exists_measW_prescribed X.B.I.F X.B.I.E X.B.I.cm.sig hCM
      X.B.I.n X.B.I.J hH D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
      (X.measW u).μNinf (X.measW u).μHinf μN μH μSv hWn.2.2.2.2.1 hWn.2.1 hN h2 hSv
    refine ⟨W, hWt, e1, e2, ⟨hT1, νH, h1, ?_⟩, ?_, ?_⟩
    · rw [e4]; exact h3
    · rw [e3]; exact hN1
    · intro v; rw [e5]; exact hSt v
  choose mw hw hNinf hHinf hOm hCov hLoc using hW
  let mg : MeasG X.B.I.cm.sig X.B.I.J D.R.rS := { X.measG with μB := μB' }
  have hg : mg.IsTextNorm := ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hμB', hG.2.2.2.2.2⟩
  refine ⟨mg, hg, mw, hw, ?_, ψ, hψ, hstd', ?_, ?_⟩
  · refine ⟨hM.1, hM.2.1, hM.2.2.1, fun u => ?_⟩
    have h := hM.2.2.2 u
    constructor
    · show amb (mw u).μNinf = _
      rw [hNinf u]; exact h.1
    · show amb (mw u).μHinf = _
      rw [hHinf u]; exact h.2
  · exact ⟨fun u => ⟨hOm u, hCov u⟩, hBc⟩
  · intro w v
    exact hLoc w v

end GlobalTheory.St.Rescale
end
