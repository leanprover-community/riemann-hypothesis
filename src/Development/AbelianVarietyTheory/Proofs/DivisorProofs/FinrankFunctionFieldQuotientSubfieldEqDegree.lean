import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyHessianDeterminantRealPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormHeightExpSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqSemilinearLeLatticeFrameNormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRImageModelSectionSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary

section
section
open GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_mul_rank (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K]
    (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K) (hι : Function.Injective ι)
    (hy : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  classical
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  letI : Algebra k K := ι.toAlgebra
  have hyk : AlgebraicIndependent k y := hy.extendScalars_of_isIntegral k
  have hinj : Function.Injective (MvPolynomial.eval₂Hom ι y) := hyk
  refine ⟨?_, hinj⟩
  haveI : CharZero k := ι.charZero
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  set F : Subfield K := ratF x with hF
  have hyF : ∀ j, y j ∈ F := fun j => Subfield.subset_closure ⟨j, rfl⟩
  set n := Module.finrank ℤ k with hn
  let b := Module.finBasis ℤ k
  set R : Subring K := Subring.closure (Set.range y) with hRdef
  have hR : R ≤ (MvPolynomial.eval₂Hom (Int.castRingHom K) y).range :=
    (Subring.closure_le).2 (by rintro _ ⟨j, rfl⟩; exact ⟨MvPolynomial.X j, by simp⟩)
  have hli : LinearIndependent F (fun i => ι (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i₀
    have hg' : ∑ i, (g i : K) * ι (b i) = 0 := hg
    have hfrac : ∀ i, ∃ a ∈ R, ∃ c ∈ R, c ≠ 0 ∧ (g i : K) = a / c := by
      intro i
      obtain ⟨a, ha, c, hc, e⟩ := Subfield.mem_closure_iff.1 (g i).2
      by_cases h0 : c = 0
      · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by rw [← e, h0, div_zero, zero_div]⟩
      · exact ⟨a, ha, c, hc, h0, e.symm⟩
    choose a ha c hc hc0 hgac using hfrac
    set Q : K := ∏ j, c j with hQdef
    have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hc0 j
    have hp : ∀ i, Q * (g i : K) = a i * ∏ j ∈ Finset.univ.erase i, c j := by
      intro i
      rw [hgac i, hQdef, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
      field_simp [hc0 i]
    have hpR : ∀ i, Q * (g i : K) ∈ R := fun i => by
      rw [hp i]; exact R.mul_mem (ha i) (Subring.prod_mem _ fun j _ => hc j)
    choose P hP using fun i => hR (hpR i)
    have hsum : ∑ i, Q * (g i : K) * ι (b i) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hg', mul_zero]
    have hcomp : ι.comp (Int.castRingHom k) = Int.castRingHom K := RingHom.ext_int _ _
    have hev : MvPolynomial.eval₂Hom ι y
        (∑ i, MvPolynomial.C (b i) * MvPolynomial.map (Int.castRingHom k) (P i)) = 0 := by
      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_map_hom, hcomp, hP]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
      ring
    have hP0 := hinj (hev.trans (map_zero _).symm)
    have hPi : ∀ i, P i = 0 := by
      intro i
      ext m
      have hm := congrArg (MvPolynomial.coeff m) hP0
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
        MvPolynomial.coeff_zero, eq_intCast] at hm
      have hm' : ∑ j, MvPolynomial.coeff m (P j) • b j = 0 := by
        rw [← hm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [zsmul_eq_mul, mul_comm]
      rw [MvPolynomial.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hm' i
    have h1 : Q * (g i₀ : K) = 0 := by rw [← hP i₀, hPi i₀, map_zero]
    exact Subtype.ext ((mul_eq_zero.1 h1).resolve_left hQ)
  have hV : Module.finrank F (Submodule.span F (Set.range fun i => ι (b i))) = n := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  let E : IntermediateField F K := IntermediateField.adjoin F (Set.range ι)
  have halg : ∀ z ∈ Set.range ι, IsAlgebraic F z := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsIntegral ℤ (ι a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map ι.toIntAlgHom
    exact (h1.tower_top (A := F)).isAlgebraic
  have hEsub : Subalgebra.toSubmodule E.toSubalgebra = Submodule.span F (Set.range fun i => ι (b i)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Algebra.adjoin_eq_span]
      refine Submodule.span_le.2 ?_
      intro z hz
      have hcl : Submonoid.closure (Set.range ι) ≤ MonoidHom.mrange ι :=
        Submonoid.closure_le.2 (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)
      obtain ⟨a, rfl⟩ := hcl hz
      have hsr := b.sum_repr a
      change ι a ∈ _
      rw [← hsr, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => ι (b i)) i)) _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin F _ ⟨b i, rfl⟩
  have hEF : Module.finrank F E = n := by
    have : Module.finrank F E = Module.finrank F (Subalgebra.toSubmodule E.toSubalgebra) := rfl
    rw [this, hEsub, hV]
  have hsub : E.toSubfield = Subfield.closure (Set.range ι ∪ Set.range y) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨z, rfl⟩
        exact (Subfield.closure_le.2 (Set.subset_union_right.trans Subfield.subset_closure)) z.2
      · exact Set.subset_union_left.trans Subfield.subset_closure
    · refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · exact fun z hz => IntermediateField.subset_adjoin F _ hz
      · rintro _ ⟨j, rfl⟩; exact E.algebraMap_mem ⟨y j, hyF j⟩
  have htow := Module.finrank_mul_finrank F E K
  have hEK : Module.finrank E.toSubfield K = Module.finrank E K := rfl
  rw [← hsub, hEK, ← htow, hEF, mul_comm]

end GlobalTheory.HSAmp
end

open GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order : ∀ (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K] (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K), Function.Injective ι → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  atlas_forward_decl GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PSpaceDeg

theorem ringKrullDim_eq_one (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ringKrullDim k = 1 := by
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := ℤ) (B := k)
    (algebraMap ℤ k).injective_int]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem isArithVar (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    IsArithVar (PSpace.str k D) D :=
  ProjModel.isArithVar_pspace k (ringKrullDim_eq_one k) D

theorem injective_ringHom {k : Type} [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (ψ : k →+* ℂ) : Function.Injective ψ := by
  refine (RingHom.injective_iff_ker_eq_bot ψ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)

def ringHomEquiv (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] [Field K]
    [Algebra k K] [IsFractionRing k K] : (k →+* ℂ) ≃ (K →+* ℂ) where
  toFun ψ := IsFractionRing.lift (injective_ringHom ψ)
  invFun φ := φ.comp (algebraMap k K)
  left_inv ψ := by
    ext x
    rw [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom ψ) x
  right_inv φ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors k) (RingHom.ext fun x => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (injective_ringHom (φ.comp (algebraMap k K))) x

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem finrank_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    [Field K] [Algebra k K] [IsFractionRing k K] [CharZero K] :
    Module.finrank ℚ K = Module.finrank ℤ k ∧ FiniteDimensional ℚ K := by
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  haveI : @IsScalarTower ℤ ℚ K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid k (nonZeroDivisors ℤ)) K := inferInstance
  let b := Module.Free.chooseBasis ℤ k
  let b' := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  exact ⟨(Module.finrank_eq_card_basis b').trans (Module.finrank_eq_card_basis b).symm,
    Module.Finite.of_basis b'⟩

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem card_ringHom (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  haveI : CharZero (FractionRing k) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
  obtain ⟨h1, h2⟩ := finrank_fractionRing k (FractionRing k)
  haveI : NumberField (FractionRing k) := ⟨⟩
  rw [Nat.card_congr (ringHomEquiv k (FractionRing k)), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card, h1]

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

open Set
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)

theorem exists_stdChart (k : Type) [CommRing k] (σ : k →+* ℂ) (N : ℕ) :
    ∃ (c : AlgChart (PSpace.str k N) σ N) (i : (ProjSpace.hermitianTwistingSheaf k N).B.ι),
      c.e.source = ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) ∧ c.e.target = Set.univ ∧
      c.e.source ⊆ ptsIn (PSpace.str k N) σ ((ProjSpace.hermitianTwistingSheaf k N).B.U i) ∧
      ∀ v, ((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  obtain ⟨c, h₁, h₂, h₃⟩ := StdProjChart.exists_of_bijective (p := PSpace.str k N) σ
    (ProjSpace.isAffineOpen_chart k N 0) _ (StdProjChart.bijective_ratio k N 0)
  refine ⟨c, (0 : Fin (N + 1)), h₁, h₂, h₁.le, fun v => ?_⟩
  have hv : c.e.symm v ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) :=
    h₁ ▸ c.e.map_target (h₂ ▸ trivial)
  have h := Weight.fsBasis_φ (p := PSpace.str k N) (σ := σ) (ProjSpace.O1_isLB k N)
    (ProjSpace.coord k N) (ProjSpace.iSup_nonzeroLocus_coord k N) 1 (by simp) (0 : Fin (N + 1))
    (c.e.symm v)
  refine h.trans ?_
  have h0 : ev (PSpace.str k N) σ (ProjSpace.chart k N 0) (ProjSpace.ratio k N 0 0)
      (c.e.symm v) = 1 := by
    simp only [ProjSpace.ratio, ProjSpace.ratioOn_self]
    rw [ev_eq hv, map_one]
  have key : ∑ a : Fin (N + 1), ‖ev (PSpace.str k N) σ (ProjSpace.chart k N 0)
      (ProjSpace.ratio k N 0 a) (c.e.symm v)‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
    rw [Fin.sum_univ_succ, h0, EuclideanSpace.norm_sq_eq]
    simp only [Fin.succAbove_zero] at h₃
    simp only [h₃, norm_one, one_pow]
  rw [← key]
  simp [Matrix.one_apply, ev]

theorem chern_mass_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (N : ℕ) (σ : k →+* ℂ) :
    ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N 1 Set.univ = 1 ∧
      ((ProjSpace.hermitianTwistingSheaf k N).φ σ).chernPart N (-1) Set.univ = 0 := by
  have hA := isArithVar k N
  have hproj : IsProjOver (PSpace.str k N) := hA.isProjOver
  haveI : IsIntegral (PSpace k N) := ProjSpace.isIntegral_of_isDomain k N
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hproj
  have hC : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).IsCInf := (ProjSpace.hermitianTwistingSheaf k N).cInf _
  have hSP : ((ProjSpace.hermitianTwistingSheaf k N).φ σ).SemiPosReg N :=
    (HermLB.semiPos_fs _ _ _ _ _ _ : (ProjSpace.hermitianTwistingSheaf k N).SemiPos N) _
  refine ⟨?_, by rw [Weight.chernPart_neg_eq_zero hC hSP]; rfl⟩
  obtain ⟨c, i, hsrc, htgt, hsub, hφv⟩ := exists_stdChart k σ N
  have hmem : c.e.symm 0 ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  have hgen : genericPoint (PSpace k N) ∈ ProjSpace.chart k N 0 := by
    have h0 : c.e.symm 0 ∈ ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0) := hsrc ▸ hmem
    exact ((genericPoint_spec (PSpace k N)).mem_open_set_iff (ProjSpace.chart k N 0).isOpen).2
      ⟨_, by simp, mem_ptsIn.1 h0⟩
  have hnull := ChernNull.chernPart_over_closed hA ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ
    (ProjSpace.chart k N 0).isOpen.isClosed_compl (by simpa using hgen) σ ((ProjSpace.hermitianTwistingSheaf k N).φ σ) 1
  have hcX : (ptsIn (PSpace.str k N) σ (ProjSpace.chart k N 0))ᶜ =
      {y : CxPts (PSpace.str k N) σ | y.1 (IsLocalRing.closedPoint ℂ) ∈
        ((ProjSpace.chart k N 0 : (PSpace k N).Opens) : Set (PSpace k N))ᶜ} := by
    ext y
    simp [mem_ptsIn]
  rw [← hcX, ← hsrc] at hnull
  have hmeas : MeasurableSet c.e.source := c.e.open_source.measurableSet
  rw [← union_compl_self c.e.source, measure_union disjoint_compl_right hmeas.compl, hnull, add_zero,
    Weight.chernPart_apply hC 1 c hmeas subset_rfl, c.e.image_source_eq_target, htgt,
    Measure.restrict_univ]
  refine Eq.trans (lintegral_congr fun v => ?_) (lintegral_fubiniStudy_density_eq_one N)
  have hv : c.e.symm v ∈ c.e.source := c.e.map_target (htgt ▸ mem_univ _)
  rw [AlgChart.chernDens_eq c hC hv (hsub hv), AlgChart.hess, c.e.right_inv (htgt ▸ mem_univ _)]
  have hf : (fun w => ((((ProjSpace.hermitianTwistingSheaf k N).φ σ).φ i (c.e.symm w) : ℝ) : ℂ)) =
      fun w => ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : ℂ) := funext fun w => by rw [hφv w]
  rw [hf, FSDet.det_fubiniStudy_hess N v]
  simp

end GlobalTheory.PSpaceDeg

namespace GlobalTheory.PSpaceDeg

theorem degree_hermitian_O_one_projective (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ) :
    gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) := by
  have hσ : ∀ σ : k →+* ℂ, ((ProjSpace.hermitianTwistingSheaf k D).φ σ).chernInt D Set.univ (fun _ => 1) = 1 := by
    intro σ
    obtain ⟨h1, h0⟩ := chern_mass_hermitian_O_one_projective k D σ
    rw [GdegPullProof.chernInt_one, h1, h0]
    simp
  haveI : Finite (k →+* ℂ) := by
    haveI : CharZero (FractionRing k) :=
      charZero_of_injective_algebraMap (IsFractionRing.injective k (FractionRing k))
    haveI : FiniteDimensional ℚ (FractionRing k) := (finrank_fractionRing k (FractionRing k)).2
    haveI : NumberField (FractionRing k) := ⟨⟩
    exact Finite.of_equiv _ (ringHomEquiv k (FractionRing k)).symm
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [gdeg, chInt, hσ]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]

theorem main : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ),
    IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧
      Nat.card (k →+* ℂ) = Module.finrank ℤ k :=
  fun k _ _ _ _ D => ⟨isArithVar k D, degree_hermitian_O_one_projective k D, card_ringHom k⟩

end GlobalTheory.PSpaceDeg
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (D : ℕ), IsArithVar (PSpace.str k D) D ∧ gdeg (ProjSpace.hermitianTwistingSheaf k D) D = Nat.card (k →+* ℂ) ∧ Nat.card (k →+* ℂ) = Module.finrank ℤ k := by
  atlas_forward_decl GlobalTheory.PSpaceDeg.main
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory

theorem isArithVar_charZero_functionField_and_injective :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
      IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  intro k _ X _ p D h
  have hΓ : CharZero Γ(X, ⊤) := h.charZero
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom :=
    germ_injective_of_isIntegral X _ _
  have hK : CharZero X.functionField := (RingHom.charZero_iff hg).1 hΓ
  refine ⟨hK, ?_⟩
  have := h.isDomain
  have := h.finite
  have hint : Algebra.IsIntegral ℤ k := inferInstance
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have : a ∈ RingHom.ker (GlobalTheory.toFunctionField p) := ha
  rw [hker] at this
  exact this

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArith_charZero_functionField_injective_constants : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  atlas_forward_decl GlobalTheory.isArithVar_charZero_functionField_and_injective
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice
open scoped Classical

namespace GlobalTheory.ImageModel

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
  {ev : V →ₗ[K] Ω} {D : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : HermLB p}
  {ψ : Ω →+* X.functionField} {s : W → L.B.Sec}

theorem IsModelOf.fs_sum_pos (hM : IsModelOf Nm W ev D p L ψ s) (hev : ev ≠ 0) {N n : ℕ} {b : Module.Basis (Fin N) K V}
    {g : Matrix (Fin N) (Fin n) K} {A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {c : Matrix (Fin n) (Fin N) K}
    {gw : Fin n → W} (hF : IsFrame Nm W b g A) (hg : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hc : ∀ j, b j = ∑ k, c k j • (gw k : V)) (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K)))
    (hy : y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i)) :
    0 < ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun hS => ?_
  obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
  have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
  have hb := GlobalTheory.frame_semilinear_sq_le K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
    (fun m β u x hx => valR_section_sum K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
  rw [← hS, mul_zero] at hb
  exact hne (by
    have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
    exact norm_eq_zero.1 this)

theorem IsModelOf.fs_shift (hM : IsModelOf Nm W ev D p L ψ s) (hev : ev ≠ 0) (t : ℝ) :
    ∃ (N n : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W),
      IsFrame (fun σ x => Real.exp (-t) * Nm σ x) W b g A ∧ (∀ k, (gw k : V) = ∑ j, g j k • b j) ∧
      (∀ j, b j = ∑ k, c k j • (gw k : V)) ∧
      ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts p (σ.comp (algebraMap (𝓞 K) K))),
        y ∈ ptsIn p (σ.comp (algebraMap (𝓞 K) K)) (L.B.U i) →
        ((L.shift (fun _ => t) (fun _ => rfl)).φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  refine ⟨N, n, b, g, fun σ => ((Real.exp t : ℝ) : ℂ) • A σ, c, gw,
    ⟨hF.span, hF.full, fun σ => ?_, fun σ x => ?_, fun σ x => ?_⟩, hg, hc, fun σ i y hy => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')) (hF.herm σ)
  · simp only [GlobalTheory.HeightShift.frameNorm_exp_smul (hF.herm _)]
    rw [hF.conj σ x]
  · rw [GlobalTheory.HeightShift.frameNorm_exp_smul (hF.herm _), hF.norm]
  · have hpos := hM.fs_sum_pos hev hF hg hc σ i y hy
    have e : ∑ a, ‖∑ k, (∑ m, σ (c k m) * (((Real.exp t : ℝ) : ℂ) • A σ) m a) *
          valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 =
        Real.exp t ^ 2 * ∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ∑ k, (∑ m, σ (c k m) * (((Real.exp t : ℝ) : ℂ) • A σ) m a) * valR y.1 (L.B.U i) ((s (gw k)).f i) =
          ((Real.exp t : ℝ) : ℂ) * ∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]; ring
      rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [e, Real.log_mul (pow_pos (Real.exp_pos _) 2).ne' hpos.ne', Real.log_pow, Real.log_exp, ← hφ σ i y]
    change (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y + 2 * t = _
    push_cast
    ring

end GlobalTheory.ImageModel
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.SelfInterImage

theorem imageHeight_exp_smul {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {D : ℕ} (hex : ∃ x, IsImageHeight Nm W ev D x) (t : ℝ) :
    imageHeight (fun σ x => Real.exp (-t) * Nm σ x) W ev D = imageHeight Nm W ev D + t := by
  have h1 := GlobalTheory.HeightShift.isImageHeight_shift K V Ω Nm W ev D _ (fun _ => t) (fun _ => rfl)
    (isImageHeight_imageHeight hex)
  have e : (∑ _σ : K →+* ℂ, t) / (Module.finrank ℚ K : ℝ) = t := by
    rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
    have : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    field_simp
  rw [e] at h1
  exact GlobalTheory.ImageHeightUnique.isImageHeight_unique (isImageHeight_imageHeight ⟨_, h1⟩) h1

end GlobalTheory.SelfInterImage
end

section
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.HermLB

theorem isometric_pull_fs_toProj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : GlobalTheory.HermLB p) (m : ℕ) (t : Fin (m + 1) → L.B.Sec) (ht : ⨆ j, nonzeroLocus (t j) = ⊤)
    (A : (k →+* ℂ) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U),
    (∀ (σ : k →+* ℂ) (i : L.B.ι) (y : GlobalTheory.CxPts p σ), y ∈ ptsIn p σ (L.B.U i) →
      (L.φ σ).φ i y = Real.log (∑ a, ‖∑ j, A σ j a * valR y.1 (L.B.U i) ((t j).f i)‖ ^ 2)) →
    ((GlobalTheory.HermLB.fs (PSpace.str k m) (GlobalTheory.ProjSpace.O1_isLB k m) (GlobalTheory.ProjSpace.coord k m) (GlobalTheory.ProjSpace.iSup_nonzeroLocus_coord k m) A hA hc).pull
      (GlobalTheory.ProjSpace.toProj p t ht) (GlobalTheory.ProjSpace.toProj_str p t ht)).Isometric L := by
  intro k _ X p L m t ht A hA hc h
  refine ⟨ProjSpace.toProjIso p t ht, ProjSpace.toProjIso_isGen p t ht, fun σ a b y ha hb => ?_⟩
  let π := ProjSpace.toProj p t ht
  have hπ : π ≫ PSpace.str k m = p := ProjSpace.toProj_str p t ht
  let z := Points.PtsOver.map π hπ (spMap σ) y
  let B := (ProjSpace.O1 k m).pull π
  have hb' : y ∈ ptsIn p σ (B.U b) := hb
  have hab : y ∈ ptsIn p σ (L.B.U a ⊓ B.U b) := mem_ptsIn_inf.2 ⟨ha, hb'⟩
  have hz : z ∈ ptsIn (PSpace.str k m) σ ((ProjSpace.O1 k m).U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => z) (fun _ => rfl) hb' PUnit.unit
  let u : Γ(X, L.B.U a ⊓ B.U b)ˣ := (ProjSpace.toProjIso p t ht).s (a, b)
  let r : Fin (m + 1) → ℂ := fun j =>
    valR z.1 ((ProjSpace.O1 k m).U (b PUnit.unit)) ((ProjSpace.coord k m j).f (b PUnit.unit))
  have hu : ev p σ _ u.val y ≠ 0 := ev_ne_zero hab u.isUnit
  have e (j) : valR y.1 (L.B.U a) ((t j).f a) = ev p σ _ u.val y * r j := by
    have e₁ : resG X (inf_le_left : L.B.U a ⊓ B.U b ≤ L.B.U a) ((t j).f a) =
        u.val * resG X inf_le_right ((Cartier.secPull (ProjSpace.coord k m j) π).f b) :=
      ProjSpace.secMaps_toProjIso p t ht j (a, b)
    have e₂ := congrArg (ev p σ _ · y) e₁
    simp only [ev_mul, ev_res _ hab] at e₂
    exact e₂.trans (congrArg (_ * ·) (Points.valR_appLE y.1 π _ hb' _))
  have h0 := (Weight.noCommonZero_combVal (p := PSpace.str k m) (σ := σ)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (hA σ)).sum_pos hz
  have h0' : 0 < ∑ c, ‖∑ j, A σ j c * r j‖ ^ 2 := h0.trans_eq (Finset.sum_congr rfl fun c _ =>
    congrArg (‖·‖ ^ 2) ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)))
  have e₃ := (Weight.pull_φ (Weight.fsBasis (PSpace.str k m) σ (ProjSpace.O1_isLB k m) (ProjSpace.coord k m)
    (ProjSpace.iSup_nonzeroLocus_coord k m) (A σ) (hA σ)) π hπ b y).trans (Weight.fsBasis_φ _ _ _ _ _ _ _)
  refine (h σ a y ha).trans (Eq.trans ?_ (congrArg (· + Real.log (‖ev p σ _ u.val y‖ ^ 2)) e₃.symm))
  refine Eq.trans ?_ (Real.log_mul h0'.ne' (pow_ne_zero 2 (norm_ne_zero_iff.2 hu)))
  rw [Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
  rw [← mul_pow, ← norm_mul, Finset.sum_mul]
  refine congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun j _ => ?_)
  rw [e j]
  ring

end GlobalTheory.HermLB
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSAmp.GenMap

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_chart {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
  Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))

theorem loc_mul_div (P : Pair p) (e : ℕ) (f ρ : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc e 0 f i j * (ρ / P.loc e 0 1 i j) = f * ρ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem loc_eq_mul_inv (P : Pair p) (e : ℕ) (f ρ : X.functionField) (hρ : ρ ≠ 0) (i : P.L.B.ι)
    (j : P.A.B.ι) : P.loc e 0 f i j = f * ρ * (ρ / P.loc e 0 1 i j)⁻¹ := by
  have := (P.r i).ne_zero
  have := (P.r' j).ne_zero
  simp only [Pair.loc]
  field_simp

theorem exists_secs (P : Pair p) {D e : ℕ} {x : Fin (D + 1) → X.functionField} (hx : Gens P D e x) :
    ∃ (ρ : (P.L.pow e).B.ι → X.functionFieldˣ) (s : Fin (D + 1) → (P.L.pow e).B.Sec),
      (∀ z c i j, z ∈ (P.L.pow e).B.U c → z ∈ P.L.B.U i → z ∈ P.A.B.U j →
        UnitAt z ((ρ c : X.functionField) / P.loc e 0 1 i j)) ∧
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) c j, y ∈ ptsIn p σ ((P.L.pow e).B.U c) → y ∈ ptsIn p σ (P.A.B.U j) →
        ‖ratVal ((ρ c : X.functionField) / P.loc e 0 1 (c PUnit.unit) j) y‖ = 1) ∧
      ∀ l c (hc : genericPoint X ∈ (P.L.pow e).B.U c), fnOf _ hc ((s l).f c) = x l * ρ c := by
  obtain ⟨ρ, hρ, hu, hn⟩ := Pair.rep_pow k X p P 1 0 P.L e (Pair.rep_base k X p P).1
  simp only [mul_one, mul_zero] at hu hn
  have hs : ∀ l, ∃ u : (P.L.pow e).B.Sec, ∀ c (hc : genericPoint X ∈ (P.L.pow e).B.U c),
      fnOf _ hc (u.f c) = x l * ρ c := fun l =>
    RepDict.exists_sec hρ fun c z hz => by
      obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
      obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
      rw [← loc_mul_div P e (x l) _ i j]
      exact (hx.mem l z i j hi hj).mul (hu z c i j hz hi hj).regAt
  choose s hs using hs
  refine ⟨ρ, s, hu, fun σ y c j hc hj => ?_, hs⟩
  have hc' := mem_pow_iff.1 hc
  have hU := hu _ c _ j (mem_ptsIn.1 hc) (mem_ptsIn.1 hc') (mem_ptsIn.1 hj)
  have h1 := hn σ y c _ j hc hc' hj
  have h2 : ((P.L.pow e).φ σ).φ c y = ((e : ℤ) : ℝ) * (P.L.φ σ).φ (c PUnit.unit) y := Weight.zpow_φ _ _ _ _
  rw [h2] at h1
  push_cast at h1
  refine Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (ratVal_ne_zero hU)) ?_
  linarith

end GlobalTheory.HSAmp.GenMap

namespace GlobalTheory.HSAmp.GenMap

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → x 0 ≠ 0 → ∃ (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D _ P e x hx hx0
  obtain ⟨ρ, s, hu, hn1, hs⟩ := exists_secs P hx
  have hnz : ∀ l z i j, z ∈ P.L.B.U i → z ∈ P.A.B.U j →
      (z ∈ Out.nonzeroLocus (s l) ↔ UnitAt z (P.loc e 0 (x l) i j)) := by
    intro l z i j hi hj
    obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB z
    have hU := hu z c i j hc hi hj
    rw [mem_nonzeroLocus_iff (s l) c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs l c (gen_mem hc)]
    exact ⟨fun h => loc_eq_mul_inv P e (x l) _ (ρ c).ne_zero i j ▸ h.mul hU.inv,
      fun h => loc_mul_div P e (x l) _ i j ▸ h.mul hU⟩
  have hcov : ⨆ l, Out.nonzeroLocus (s l) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := mem_chart P.L.isLB z
    obtain ⟨j, hj⟩ := mem_chart P.A.isLB z
    obtain ⟨l, hl⟩ := hx.cover z
    exact Opens.mem_iSup.2 ⟨l, (hnz l z i j hi hj).2 (hl i j hi hj)⟩
  obtain ⟨c, hc⟩ := mem_chart (P.L.pow e).isLB (genericPoint X)
  have hη : genericPoint X ∈ Out.nonzeroLocus (s 0) := by
    rw [mem_nonzeroLocus_iff (s 0) c hc, X.mem_basicOpen _ _ hc]
    show IsUnit (fnOf _ hc ((s 0).f c))
    rw [hs 0 c hc]
    exact isUnit_iff_ne_zero.2 (mul_ne_zero hx0 (ρ c).ne_zero)
  have hpre := ProjSpace.toProj_preimage_chart p s hcov 0
  have hmem : genericPoint X ∈ ProjSpace.toProj p s hcov ⁻¹ᵁ ProjSpace.chart k D 0 := by
    rw [hpre]; exact hη
  refine ⟨ProjSpace.toProj p s hcov, ProjSpace.toProj_str p s hcov, ⟨hmem, fun j => ?_⟩, fun u hu' => ?_⟩
  · change fnOf _ hmem _ = _
    rw [ProjSpace.pullRatio_toProj_on p s hcov 0 j le_rfl, fnOf_resG]
    have hc' : genericPoint X ∈ Out.nonzeroLocus (s 0) ⊓ (P.L.pow e).B.U c := ⟨hη, hc⟩
    have e1 := congrArg (fnOf _ hc') (ProjSpace.secRatio_spec (s 0) (s j) c)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hs j c hc, hs 0 c hc] at e1
    rw [eq_div_iff hx0]
    refine mul_right_cancel₀ (ρ c).ne_zero ?_
    linear_combination -e1
  · have he : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hx.pos.ne'
    refine (HermLB.isometric_pull_fs_toProj k X p ((up P.L u).pow e) D s hcov (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩) ?_).symm
    intro σ i y hy
    change y ∈ ptsIn p σ ((P.L.pow e).B.U i) at hy
    have hy' : y ∈ ptsIn p σ (P.L.B.U (i PUnit.unit)) := mem_pow_iff.1 hy
    have hj : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
    have hg := hn1 σ y i _ hy hj
    have hA : ∀ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ := fun l => by
      have hη := gen_mem (mem_ptsIn.1 hy)
      change ‖ev p σ _ ((s l).f i) y‖ = _
      rw [← ratVal_fnOf hy hη, hs l i hη, ← loc_mul_div P e (x l) _ (i PUnit.unit) _,
        ratVal_mul (hx.mem l _ _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj))
          (hu _ i _ _ (mem_ptsIn.1 hy) (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)).regAt, norm_mul, hg, mul_one]
    have hnu : ∀ l, P.nu e 0 σ y (x l) ^ 2 =
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 *
          Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) := fun l => by
      rw [nu_eq k X p P e 0 (x l) (hx.mem l) σ y _ _ hy' hj, mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    set S := ∑ l, ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2 with hS
    have hSpos : 0 < S := by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      have h0 := norm_pos_iff.2 (ratVal_ne_zero (hl _ _ (mem_ptsIn.1 hy') (mem_ptsIn.1 hj)))
      exact (pow_pos h0 2).trans_le (Finset.single_le_sum (f := fun l =>
        ‖ratVal (P.loc e 0 (x l) (i PUnit.unit) (pick (P.A.φ σ).isLB y)) y‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ l))
    have hsum : ∑ l, P.nu e 0 σ y (x l) ^ (2 * 1) = Real.exp (-((e : ℝ) * (P.L.φ σ).φ (i PUnit.unit) y)) * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_one, hnu l, mul_comm]
    have hu1 := hu' σ y
    rw [hsum, Real.log_mul (Real.exp_pos _).ne' hSpos.ne', Real.log_exp] at hu1
    change (((P.L.φ σ).addFn (u.u σ)).zpow (e : ℤ)).φ i y = _
    refine (Weight.zpow_φ _ _ _ _).trans ?_
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    change ((e : ℤ) : ℝ) * ((P.L.φ σ).φ (i PUnit.unit) y + u.u σ y) =
      Real.log (∑ l, ‖valR y.1 ((P.L.pow e).B.U i) ((s l).f i)‖ ^ 2)
    simp only [hA, ← hS]
    rw [hu1]
    push_cast
    field_simp
    ring

end GlobalTheory.HSAmp.GenMap
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_projSpace_basepointFreeSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → x 0 ≠ 0 → ∃ (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  atlas_forward_decl GlobalTheory.HSAmp.GenMap.toProj_gens
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.GenericImage

open scoped GlobalTheory.ProjSpace

theorem map_genericPoint_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  intro k _ X _ p D _ π hπ x hx0 ⟨h, hx⟩ hinj
  set W := π ⁻¹ᵁ ProjSpace.chart k D 0 with hW
  let Φ : Γ(PSpace k D, ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ W (genericPoint X) h).hom.comp (π.appLE (ProjSpace.chart k D 0) W le_rfl).hom
  have hconst : (X.presheaf.germ W (genericPoint X) h).hom.comp
      (GlobalTheory.QCoh.Qcqs.baseRingHom (π ≫ PSpace.str k D) W).hom = GlobalTheory.toFunctionField p := by
    subst hπ
    refine RingHom.ext fun a => ?_
    simp only [GlobalTheory.QCoh.Qcqs.baseRingHom, GlobalTheory.toFunctionField, Scheme.Hom.appLE, CommRingCat.hom_comp,
      RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  have key : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 → Φ a ≠ 0 := by
    intro a ha
    obtain ⟨P, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 a
    let s : Fin (D + 1) → MvPolynomial (Fin D) k := Fin.cons 1 MvPolynomial.X
    have e1 : ∀ (A : Type) [CommRing A] (c : k →+* A) (r : Fin (D + 1) → A), r 0 = 1 →
        MvPolynomial.eval₂Hom c r P =
          MvPolynomial.eval₂Hom c (fun j : Fin D => r j.succ) (MvPolynomial.bind₁ s P) := by
      intro A _ c r hr
      rw [MvPolynomial.eval₂Hom_bind₁]
      congr 2
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [s, hr]
      · simp [s]
    have e2 : Φ (MvPolynomial.aeval (ProjSpace.ratio k D 0) P) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) P := by
      have := congrArg (fun t => t P) (ProjSpace.appLE_comp_aeval_ratio (φ := π) (W := W) (i := 0) (hi := le_rfl))
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this
      simp only [Φ, RingHom.comp_apply]
      erw [this]
      rw [MvPolynomial.map_eval₂Hom, hconst]
      congr 2
      funext j
      exact hx j
    rw [e2, e1 _ _ _ (div_self hx0)]
    intro h0
    have hQ : MvPolynomial.bind₁ s P = 0 := hinj (h0.trans (map_zero _).symm)
    apply ha
    rw [MvPolynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom,
      e1 _ _ _ (by rw [ProjSpace.ratio, ProjSpace.ratioOn_self]), hQ, map_zero]
  have hmem : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 →
      π (genericPoint X) ∈ (PSpace k D).basicOpen a := by
    intro a ha
    have h1 : genericPoint X ∈ X.basicOpen ((π.appLE (ProjSpace.chart k D 0) W le_rfl).hom a) := by
      rw [Scheme.mem_basicOpen X _ _ h]
      exact (key a ha).isUnit
    have h2 := (Scheme.basicOpen_appLE π W _ le_rfl a).le h1
    exact h2.2
  refine IsGenericPoint.eq ?_ (genericPoint_spec _)
  refine Dense.closure_eq (dense_iff_inter_open.2 fun U hU hne => ?_)
  obtain ⟨y, -, hyU, hyc⟩ := (IrreducibleSpace.isIrreducible_univ (PSpace k D)).2 U
    (ProjSpace.chart k D 0 : Set (PSpace k D)) hU (ProjSpace.chart k D 0).2
    (by simpa using hne) ⟨π (genericPoint X), trivial, h⟩
  obtain ⟨f, hf, hyf⟩ := (ProjSpace.isAffineOpen_chart k D 0).exists_basicOpen_le
    (V := ⟨U, hU⟩) ⟨y, hyU⟩ hyc
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  exact ⟨_, hf (hmem f hf0), rfl⟩

end GlobalTheory.GenericImage
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  atlas_forward_decl GlobalTheory.GenericImage.map_genericPoint_eq
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section

open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace

namespace GlobalTheory.GenericResidueDegree

theorem residue_generic_bijective (X : Scheme.{0}) [IsIntegral X] :
    Function.Bijective (X.residue (genericPoint X)).hom :=
  ⟨RingHom.injective (R := X.functionField) (X.residue (genericPoint X)).hom, X.residue_surjective _⟩

theorem residueDegree_eq_finrank_closure {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (h : genericPoint X ∈ π ⁻¹ᵁ U) (E : Subfield X.functionField)
    (hE : E = Subfield.closure (Set.range fun s : Γ(Y, U) =>
      (X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) : X.functionField))) :
    π.residueDegree (genericPoint X) = Module.finrank E X.functionField := by
  let e : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom (residue_generic_bijective X)
  let ψ : Y.residueField (π (genericPoint X)) →+* X.functionField :=
    e.symm.toRingHom.comp (π.residueFieldMap (genericPoint X)).hom
  have hψ : ∀ a : Y.presheaf.stalk (π (genericPoint X)),
      ψ (Y.residue _ a) = π.stalkMap (genericPoint X) a := fun a => by
    apply e.injective
    have := congrArg (fun φ => φ.hom a) (Scheme.residue_residueFieldMap π (genericPoint X))
    exact (e.apply_symm_apply _).trans this
  have hg : ∀ s : Γ(Y, U), ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) =
      X.presheaf.germ (π ⁻¹ᵁ U) (genericPoint X) h (π.app U s) := fun s => by
    rw [hψ]
    exact π.germ_stalkMap_apply U _ h s
  have hr : ψ.fieldRange = E := by
    subst hE
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := Y.residue_surjective _ b
      letI := Y.presheaf.algebra_section_stalk (⟨π (genericPoint X), h⟩ : U)
      have hl := hU.isLocalization_stalk ⟨π (genericPoint X), h⟩
      obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (hU.primeIdealOf ⟨π (genericPoint X), h⟩).asIdeal.primeCompl a
      have hu := IsLocalization.map_units (Y.presheaf.stalk (π (genericPoint X))) t
      have h1 : ψ (Y.residue _ a) * ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) =
          ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h s)) := by
        rw [← map_mul, ← map_mul]
        exact congrArg (fun z => ψ (Y.residue _ z)) hst
      have h2 : ψ (Y.residue _ (Y.presheaf.germ U (π (genericPoint X)) h t.1)) ≠ 0 :=
        ((hu.map (Y.residue _).hom).map ψ).ne_zero
      rw [eq_div_of_mul_eq h2 h1, hg, hg]
      exact Subfield.div_mem _ (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
    · rintro _ ⟨s, rfl⟩
      exact ⟨_, hg s⟩
  clear hE
  subst hr
  letI := (π.residueFieldMap (genericPoint X)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  refine Algebra.finrank_eq_of_equiv_equiv ψ.rangeRestrictFieldEquiv e.symm ?_
  ext a
  rfl

theorem residueDegree_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  intro k _ X _ p D _ π hπ x hx ⟨h, hj⟩ _
  refine residueDegree_eq_finrank_closure π _ (ProjSpace.isAffineOpen_chart k D 0) h _ ?_
  let g : Γ(X, π ⁻¹ᵁ ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h).hom
  have hc : ∀ a : k, g ((baseRingHom (π ≫ PSpace.str k D) (π ⁻¹ᵁ ProjSpace.chart k D 0)).hom a) =
      GlobalTheory.toFunctionField p a := fun a => by
    rw [hπ]
    exact X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) h
      (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a))
  have key : ∀ q : MvPolynomial (Fin (D + 1)) k,
      g (π.app _ (MvPolynomial.aeval (R := k) (ProjSpace.ratio k D 0) q)) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) q := fun q => by
    have e₁ := congrArg (fun t => g (t q))
      (ProjSpace.appLE_comp_aeval_ratio (φ := π) (i := 0) (hi := le_rfl))
    rw [Scheme.Hom.app_eq_appLE]
    refine e₁.trans ?_
    rw [MvPolynomial.map_eval₂Hom]
    congr 2
    · exact RingHom.ext hc
    · exact funext hj
  refine le_antisymm (Subfield.closure_le.2 ?_) (Subfield.closure_le.2 ?_)
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.C a)).trans (MvPolynomial.eval₂Hom_C _ _ _)⟩
    · exact Subfield.subset_closure ⟨_, (key (MvPolynomial.X j.succ)).trans (MvPolynomial.eval₂Hom_X' _ _ _)⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 s
    refine Set.mem_of_eq_of_mem (key q) ?_
    rw [SetLike.mem_coe]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add q q' h1 h2 =>
      rw [map_add]
      exact Subfield.add_mem _ h1 h2
    | mul_X q j h1 =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine Subfield.mul_mem _ h1 ?_
      refine Fin.cases ?_ (fun j => Subfield.subset_closure (Or.inr ⟨j, rfl⟩)) j
      rw [div_self hx]
      exact Subfield.one_mem _

end GlobalTheory.GenericResidueDegree
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → π (genericPoint X) = genericPoint (PSpace k D) → π.residueDegree (genericPoint X) = Module.finrank (Subfield.closure (Set.range (GlobalTheory.toFunctionField p) ∪ Set.range fun j : Fin D => x j.succ / x 0)) X.functionField := by
  atlas_forward_decl GlobalTheory.GenericResidueDegree.residueDegree_eq_finrank_quotients
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D hX P hA e x hg
  obtain ⟨hx, hind, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hg
  obtain ⟨hK, hι⟩ := GlobalTheory.T.projArith_charZero_functionField_injective_constants k X p D hX
  haveI := hX.isDomain
  haveI := hX.finite
  haveI : CharZero k := ⟨fun a b h => Nat.cast_injective (R := X.functionField) (by
    have := congrArg (GlobalTheory.toFunctionField p) h
    simpa only [map_natCast] using this)⟩
  obtain ⟨hP, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  haveI : IsIntegral (PSpace k D) := hP.isIntegral
  obtain ⟨hdeg, hev⟩ := GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order k X.functionField (GlobalTheory.toFunctionField p) D x hι hind
  obtain ⟨π, hπ, hc, hiso⟩ := GlobalTheory.T.exists_morphism_projSpace_basepointFreeSections k X p D hX P e x hg (hx 0)
  have hgen := GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients k X p D π hπ x (hx 0) hc hev
  have hr := GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients k X p D π hπ x (hx 0) hc hgen
  refine ⟨inferInstance, π, hπ, hgen, ?_, ?_, hiso⟩
  · rw [hr]
    intro h0
    haveI := hfin
    have : 0 < Module.finrank (ratF x) X.functionField := Module.finrank_pos
    rw [hdeg, h0, zero_mul] at this
    exact lt_irrefl _ this
  · rw [hr, hdeg]

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  atlas_forward_decl GlobalTheory.HSAmp.toProj_gens
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_gdeg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  intro hA k _ X _ p D hX P hamp e x hg
  haveI := hX.isDomain
  haveI := hX.finite
  haveI := hX.charZero_base
  obtain ⟨hI, π, hπ, hgen, hr0, hr, hiso⟩ := GlobalTheory.T.exists_projectiveSpace_morphism_of_generating_sections k X p D hX P hamp e x hg
  obtain ⟨B, -, hB⟩ := GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference k X p D hX P e x hg
  obtain ⟨u, hu, -⟩ := hB 1 le_rfl
  have h1 := (hiso u hu).gdeg_eq D
  obtain ⟨hPV, hdeg, hcard⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  have h2 := (GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow hA k (PSpace k D) (PSpace.str k D) D hPV).1 X p hX π hπ hgen hr0 (ProjSpace.hermitianTwistingSheaf k D)
  have h3 : gdeg ((up P.L u).pow e) D = (e : ℝ) ^ D * gdeg (up P.L u) D :=
    GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up P.L u) e fun _ _ => 1
  have h4 := GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight hA k X p D hX P.L u
  rw [← hr]
  push_cast
  rw [← hcard, ← hdeg, ← h2, ← h1, h3, h4]

end GlobalTheory.HSAmp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_functionField_quotientSubfield_eq_degree : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (Module.finrank (ratF x) X.functionField : ℝ) = (e : ℝ) ^ D * gdeg P.L D := by
  atlas_forward_decl GlobalTheory.HSAmp.finrank_ratF_eq_gdeg
end
