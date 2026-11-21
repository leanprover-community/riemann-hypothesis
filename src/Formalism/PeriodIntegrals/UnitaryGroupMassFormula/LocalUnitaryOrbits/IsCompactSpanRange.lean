import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementA

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology
  Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem smul_eq_sc (r : Fv F v) (x : Fv F v ⊗[F] E) : r • x = sc (E := E) v r * x := by
  rw [Algebra.smul_def]
  rfl

theorem sc_mul (r s : Fv F v) : sc (E := E) v r * sc (E := E) v s = sc (E := E) v (r * s) := by
  unfold sc
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem mem_uniformizer_hermitian_ideal (ϖ : Fv F v) (h0 : ϖ ≠ 0) (a : ℕ) (z : HermR (Fv F v) σ a) :
    z ∈ hN σ v ϖ a 0 ↔ ∀ i j, (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ PO (E := E) v ϖ := by
  unfold hN
  rw [PI.VolStabSW.mem_smulSub]
  constructor
  · rintro ⟨p, hp, rfl⟩ i j
    refine ⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩
    rw [PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, pow_one, smul_eq_sc]
  · intro hz
    refine ⟨ϖ⁻¹ • z, ?_, ?_⟩
    · intro i j
      obtain ⟨c, hc, e⟩ := hz i j
      show ((ϖ⁻¹ • z : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v
      rw [PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, e, smul_eq_sc, ← mul_assoc, sc_mul,
        inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hc
    · rw [pow_one, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem latLoc_smul {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {x : Fin n → Fv F v ⊗[F] E}
    (hx : x ∈ latLoc (E := E) v Λ) : r • x ∈ latLoc (E := E) v Λ :=
  (latLoc (E := E) v Λ).smul_mem ⟨r, hr⟩ hx

theorem lamS_smul {a : ℕ} {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {x : TupV (E := E) v n a}
    (hx : x ∈ lamS v Λ a) : r • x ∈ lamS v Λ a :=
  fun i => latLoc_smul v Λ hr (hx i)

theorem fibU'_of (a : ℕ) (Y : TupV (E := E) v n a) (h1 : LamOC v Λ a) (h2 : HermOC σ v a)
    (h3 : FibHens σ J ψ v Λ a Y) : FibU' σ J ψ v Λ a Y := by
  intro hG hW hH hfib ϖ hϖ
  have hG' := hG
  obtain ⟨hS, hL, hSD, hUn, ha, hP, hdet⟩ := hG
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨hLo, hLc⟩ := h1 hL
  obtain ⟨hHo', hHc'⟩ := h2
  have := PI.VolStabSW.secondCountable_Fv F v
  have := PI.VolStabSW.locallyCompact_Fv F v
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hμ : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    unfold dX; rw [dif_pos hW]; exact hW.choose_spec
  have hν : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    unfold dT; rw [dif_pos hH]; exact hH.choose_spec
  have := hμ.1
  have := hν.1
  have hfibC : IsOm σ J ψ v a (omFam σ J ψ v a) := by
    unfold omFam; rw [dif_pos hfib]; exact hfib.choose_spec
  have hTm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ Y
  have hom : omAt σ J ψ v (gramR (Fv F v) σ J Y) =
      omFam σ J ψ v a (PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y) := by
    unfold omAt; rw [dif_pos hTm]; rfl
  rw [hom]
  set G := PI.VolStabSW.gramH (n := a) (Fv F v) σ hσ J hJ with hGdef
  set T := G Y with hTdef
  set fb := omFam σ J ψ v a with hfb

  have hΛL : lamN v Λ ϖ a 0 ≤ lamS v Λ a := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hx
    exact lamS_smul v Λ (pow_mem hint _) hp
  have hΛo : ∀ k, IsOpen (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hLo
  have hΛc : ∀ k, IsCompact (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hLc
  have hΛa : Antitone (lamN v Λ ϖ a) := by
    intro m k hmk x hx
    simp only [lamN, PI.VolStabSW.mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨ϖ ^ (k - m) • p, lamS_smul v Λ (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  have hHo : ∀ k, IsOpen (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hHo'
  have hHc : ∀ k, IsCompact (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hHc'
  have hHb : ∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ k, (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) ⊆ N' := by
    intro N hN'
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (hermOE σ v a : Set (HermR (Fv F v) σ a))
      hHc' (fun k => ϖ ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN'
    refine ⟨k, ?_⟩
    simp only [hN, PI.VolStabSW.coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp

  set Nb : Set (HermR (Fv F v) σ a) := {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
    with hNbdef
  have hTu : T ∈ Nb := by
    obtain ⟨w, -, -, hw⟩ := hdet
    exact IsUnit.of_mul_eq_one _ hw
  have hNb : Nb ∈ 𝓝 T :=
    (PI.VolStabSW.isOpen_unitHerm (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v) σ a).mem_nhds hTu
  have hNbU : ∀ x ∈ LamT v Λ a, G x ∈ Nb → x ∈ IndepV (E := E) (n := n) v a := fun x _ hx =>
    PI.VolStabSW.linIndep_of_isUnit_det (Fv F v) σ J x hx
  have hLcl : IsClosed (LamT v Λ a) := AddSubgroup.isClosed_of_isOpen (lamS v Λ a) hLo
  have e := PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1
    (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G
    (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a)
    Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo hLc (lamN v Λ ϖ a) (hN σ v ϖ a) hΛL hΛo hΛc
    hΛa hHo hHc hHb (LamT v Λ a) subset_rfl (fun y hy Z hZ => (lamS v Λ a).add_mem hy (hΛL hZ))
    hLo hLcl Nb hNb hNbU (fun y hy hyT => h3 hG' ϖ hϖ hσ hJ y hy hyT)
  have hA : LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} =
      LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mem_uniformizer_hermitian_ideal σ v ϖ h0]
    rfl
  have hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ := by
    ext z
    exact mem_uniformizer_hermitian_ideal σ v ϖ h0 a z
  rw [hA, hHP] at e
  have hLm : MeasurableSet (LamT v Λ a) := hLo.measurableSet
  have hind : (LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℂ) =
      fun x => (((LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ LamT v Λ a <;> simp [Set.indicator, hx]
  rw [hind, integral_complex_ofReal, integral_indicator_one hLm] at e
  have e' := Complex.ofReal_injective e

  have hGc : Continuous G := PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ
  obtain ⟨k, hk⟩ := hHb _ ((continuous_const.add continuous_id :
    Continuous fun w : HermR (Fv F v) σ a => T + w).continuousAt.preimage_mem_nhds
      (by simpa using hNb))
  set Q := LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a k} with hQdef
  have hQo : IsOpen Q :=
    hLo.inter (((hHo k).preimage (continuous_id.sub continuous_const)).preimage hGc)
  have hQcl : IsClosed Q :=
    hLcl.inter (((AddSubgroup.isClosed_of_isOpen _ (hHo k)).preimage
      (continuous_id.sub continuous_const)).preimage hGc)
  have hQc : IsCompact Q := hLc.of_isClosed_subset hQcl Set.inter_subset_left
  have hQU : Q ⊆ IndepV (E := E) (n := n) v a := by
    rintro x ⟨hx, hxk⟩
    refine hNbU x hx ?_
    have := hk hxk
    have e2 : G x = T + (G x - T) := by abel
    rw [e2]
    exact this
  set φ : TupV (E := E) v n a → ℝ := Q.indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hQcl, hQo⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' hQc hQcl fun x hx => Set.indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ IndepV (E := E) (n := n) v a :=
    (closure_minimal Set.support_indicator_subset hQcl).trans hQU
  obtain ⟨hint', -⟩ := hfibC.2.2 φ hφc hφs hφU
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hfinQ : fb T Q ≠ ⊤ := by
    have h := hint' T (Set.mem_univ _)
    rw [hφdef, integrable_indicator_iff hQm] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne
  have hsub : LamT v Λ a ⊆ Q ∪ (gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩
      IndepV (E := E) (n := n) v a)ᶜ := by
    intro x hx
    by_cases h : x ∈ gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩
      IndepV (E := E) (n := n) v a
    · left
      refine ⟨hx, ?_⟩
      have hGx : G x = T := Subtype.ext h.1
      show G x - T ∈ hN σ v ϖ a k
      rw [hGx, sub_self]
      exact zero_mem _
    · right
      exact h
  have hz := hfibC.1 T
  have hfin : fb T (LamT v Λ a) ≠ ⊤ := by
    refine ((measure_mono hsub).trans_lt (lt_of_le_of_lt (measure_union_le _ _) ?_)).ne
    rw [hz, add_zero]
    exact hfinQ.lt_top
  have hR : dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) /
      dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ?_ ?_).ne
    · exact ((measure_mono Set.inter_subset_left).trans_lt hLc.measure_lt_top).ne
    · rw [← hHP]
      exact ((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'
  rw [measureReal_def] at e'
  exact (ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology
  Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_span_range {ι M : Type} [Fintype ι] [AddCommGroup M] [Module (Fv F v) M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul (Fv F v) M] (w : ι → M) :
    IsCompact ((Submodule.span (v.adicCompletionIntegers F) (Set.range w) :
      Submodule (v.adicCompletionIntegers F) M) : Set M) := by
  have : CompactSpace (v.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hc : Continuous (fun c : ι → v.adicCompletionIntegers F => ∑ i, ((c i : Fv F v)) • w i) :=
    continuous_finsetSum _ fun i _ =>
      (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const
  have e : ((Submodule.span (v.adicCompletionIntegers F) (Set.range w) :
      Submodule (v.adicCompletionIntegers F) M) : Set M) =
      Set.range (fun c : ι → v.adicCompletionIntegers F => ∑ i, ((c i : Fv F v)) • w i) := by
    ext x
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    rfl
  rw [e]
  exact isCompact_range hc

theorem oEv_eq_span : OEv (E := E) v = ((Submodule.span (v.adicCompletionIntegers F)
    (Set.range (fun i => inclR (F := F) (Fv F v) ((RingOfIntegers.basis E i : 𝓞 E) : E)))) :
      Set (Fv F v ⊗[F] E)) := by
  unfold OEv
  congr 1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, -, rfl⟩
    have hx := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr x)
    rw [map_sum] at hx
    simp only [map_zsmul] at hx
    show inclR (F := F) (Fv F v) (algebraMap (𝓞 E) E x) ∈ _
    rw [← hx, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Set.mem_univ _, rfl⟩

theorem isCompact_oEv : IsCompact (OEv (E := E) v) := by
  rw [oEv_eq_span]
  exact isCompact_span_range v _

theorem isOpen_oEv : IsOpen (OEv (E := E) v) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set b := Module.finBasis F E with hb
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image b)
  have hyb : ∀ k, IsIntegral ℤ (y • b k) := fun k =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  set c : Fv F v := algebraMap F (Fv F v) (y : F) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ne_eq, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]
    exact_mod_cast hy0
  set W : Set (Fv F v ⊗[F] E) := ⋂ k, (fun z => PI.VolStabSW.PositiveNearLattice.crd b (Fv F v) z k * c⁻¹) ⁻¹'
    (v.adicCompletionIntegers F : Set (Fv F v)) with hWdef
  have hWo : IsOpen W := isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage
      ((PI.VolStabSW.PositiveNearLattice.continuous_crd b (Fv F v) k).mul continuous_const)
  have hW0 : (0 : Fv F v ⊗[F] E) ∈ W := by
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage]
    intro k
    simp [PI.VolStabSW.PositiveNearLattice.crd]
  have hWsub : W ⊆ OEv (E := E) v := by
    intro z hz
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage] at hz
    rw [PI.VolStabSW.PositiveNearLattice.eq_sum_crd b (Fv F v) z]
    unfold OEv
    refine Submodule.sum_mem _ fun k _ => ?_
    have e1 : PI.VolStabSW.PositiveNearLattice.crd b (Fv F v) z k • ((1 : Fv F v) ⊗ₜ[F] b k) =
        (PI.VolStabSW.PositiveNearLattice.crd b (Fv F v) z k * c⁻¹) • inclR (F := F) (Fv F v) (y • b k) := by
      have e2 : inclR (F := F) (Fv F v) (y • b k) = c • ((1 : Fv F v) ⊗ₜ[F] b k) := by
        show (1 : Fv F v) ⊗ₜ[F] (y • b k) = c • ((1 : Fv F v) ⊗ₜ[F] b k)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hcdef, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul, Int.cast_smul_eq_zsmul]
      rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [e1]
    have hgen : inclR (F := F) (Fv F v) (y • b k) ∈ Submodule.span (v.adicCompletionIntegers F)
        ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) :=
      Submodule.subset_span ⟨(⟨y • b k, hyb k⟩ : 𝓞 E), Set.mem_univ _, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hz k⟩ : v.adicCompletionIntegers F) hgen
  have hP : ((Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).toAddSubgroup :
        Set (Fv F v ⊗[F] E)) ∈ 𝓝 (0 : Fv F v ⊗[F] E) :=
    Filter.mem_of_superset (hWo.mem_nhds hW0) hWsub
  exact AddSubgroup.isOpen_of_mem_nhds _ hP

theorem hermOC_holds (σ : E →ₐ[F] E) (a : ℕ) : HermOC σ v a := by
  have := PI.VolStabSW.locallyCompact_Fv F v
  set S : Set (Fin a → Fin a → Fv F v ⊗[F] E) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => OEv (E := E) v with hS
  have hSe : (hermOE σ v a : Set (HermR (Fv F v) σ a)) = Subtype.val ⁻¹' S := by
    ext z
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hc : Continuous (fun z : HermR (Fv F v) σ a => (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    continuous_subtype_val
  constructor
  · rw [hSe]
    exact IsOpen.preimage hc (isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => isOpen_oEv v)
  · rw [hSe]
    exact (PI.VolStabSW.isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_oEv v)

variable {n : ℕ} (Λ : Set (Fin n → E))

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i
  simp [ratV, map_add]

theorem ratV_zsmul (c : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (c • x) = c • ratV (F := F) (Fv F v) x := by
  funext i
  simp [ratV]

theorem ratV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem isCompact_latLoc
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  obtain ⟨L, hLat, rfl⟩ := hL
  have hfg : (L.restrictScalars ℤ).FG := hLat.fg.restrictScalars
  obtain ⟨s, hs⟩ := hfg
  have e : latLoc (E := E) v (L : Set (Fin n → E)) = Submodule.span (v.adicCompletionIntegers F)
      (Set.range (fun x : s => ratV (F := F) (Fv F v) (x : Fin n → E))) := by
    apply le_antisymm
    · unfold latLoc
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by
        rw [hs]
        exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
      | zero =>
        rw [ratV_zero]
        exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        rw [ratV_add]
        exact Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [ratV_zsmul]
        exact zsmul_mem hy c
    · rw [Submodule.span_le]
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      have hxL : x ∈ L := by
        have : x ∈ L.restrictScalars ℤ := by
          rw [← hs]
          exact Submodule.subset_span hx
        exact this
      exact Submodule.subset_span ⟨x, hxL, rfl⟩
  rw [e]
  exact isCompact_span_range v _

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (L : Set (Fin n → E))) : ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.FirstStatementA.main L x hx

theorem isOpen_latLoc
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  obtain ⟨L, hLat, rfl⟩ := hL
  have hsp := hLat.span_eq_top
  have hm : ∀ i : Fin n, ∃ m : ℤ, m ≠ 0 ∧ m • (Pi.single i (1 : E) : Fin n → E) ∈ L := fun i =>
    exists_int_smul_mem L _ (by rw [hsp]; exact Submodule.mem_top)
  choose m hm0 hmL using hm
  set N : ℤ := ∏ i, m i with hNdef
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i
  have hNL : ∀ i, N • (Pi.single i (1 : E) : Fin n → E) ∈ L := by
    intro i
    have e : N = (∏ j ∈ Finset.univ.erase i, m j) * m i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [e, mul_smul]
    exact zsmul_mem (hmL i) _
  set c : Fv F v := algebraMap F (Fv F v) (N : F) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ne_eq, map_eq_zero_iff _ (algebraMap F (Fv F v)).injective]
    exact_mod_cast hN0
  have hkey : ∀ i, ∀ o ∈ OEv (E := E) v, c • (Pi.single i o : Fin n → Fv F v ⊗[F] E) ∈
      latLoc (E := E) v (L : Set (Fin n → E)) := by
    intro i o ho
    unfold OEv at ho
    rw [SetLike.mem_coe] at ho
    induction ho using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, rfl⟩ := hy
      have hxL : (x : E) • (N • (Pi.single i (1 : E) : Fin n → E)) ∈ L := by
        have h := L.smul_mem x (hNL i)
        rwa [← algebraMap_smul E x] at h
      have e : c • (Pi.single i (inclR (F := F) (Fv F v) (x : E)) : Fin n → Fv F v ⊗[F] E) =
          ratV (F := F) (Fv F v) ((x : E) • (N • (Pi.single i (1 : E) : Fin n → E))) := by
        funext j
        by_cases hij : j = i
        · subst hij
          simp only [Pi.smul_apply, Pi.single_eq_same, ratV]
          show c • ((1 : Fv F v) ⊗ₜ[F] (x : E)) = (1 : Fv F v) ⊗ₜ[F] ((x : E) • (N • (1 : E)))
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hcdef, Algebra.algebraMap_eq_smul_one,
            TensorProduct.smul_tmul]
          congr 1
          rw [Algebra.smul_def, map_intCast, zsmul_eq_mul, mul_one, smul_eq_mul, mul_comm]
        · simp [ratV, hij, inclR]
      rw [e]
      exact Submodule.subset_span ⟨_, hxL, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [Pi.single_add, smul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      have e : c • (Pi.single i (r • y) : Fin n → Fv F v ⊗[F] E) =
          r • (c • (Pi.single i y : Fin n → Fv F v ⊗[F] E)) := by
        rw [Pi.single_smul', smul_comm]
      rw [e]
      exact Submodule.smul_mem _ r hy
  set W : Set (Fin n → Fv F v ⊗[F] E) := ⋂ i, (fun y : Fin n → Fv F v ⊗[F] E => c⁻¹ • y i) ⁻¹'
    OEv (E := E) v with hWdef
  have hWo : IsOpen W := isOpen_iInter_of_finite fun i =>
    (isOpen_oEv v).preimage ((continuous_apply i).const_smul c⁻¹)
  have hW0 : (0 : Fin n → Fv F v ⊗[F] E) ∈ W := by
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage, Pi.zero_apply, smul_zero]
    exact fun _ => oEv_zero v
  have hWsub : W ⊆ latLoc (E := E) v (L : Set (Fin n → E)) := by
    intro y hy
    simp only [hWdef, Set.mem_iInter, Set.mem_preimage] at hy
    have e : y = ∑ i, c • (Pi.single i (c⁻¹ • y i) : Fin n → Fv F v ⊗[F] E) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul', smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => hkey i _ (hy i)
  exact AddSubgroup.isOpen_of_mem_nhds (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup
    (Filter.mem_of_superset (hWo.mem_nhds hW0) hWsub)

theorem lamOC_holds (a : ℕ) : LamOC v Λ a := by
  intro hL
  have e : LamT v Λ a = Set.pi Set.univ fun _ => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  rw [e]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latLoc v Λ hL,
    isCompact_univ_pi fun _ => isCompact_latLoc v Λ hL⟩

end PI.OmLocU
end
end
