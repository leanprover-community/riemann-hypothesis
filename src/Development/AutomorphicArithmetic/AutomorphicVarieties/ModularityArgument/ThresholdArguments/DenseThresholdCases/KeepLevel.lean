import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.JumpsAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedSs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.FixedUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.GalOfCusp
namespace UpperTheory.V.Af.JumpsAbove
variable {l : ℕ} [Fact l.Prime]
private theorem char_mult (K L : FinExt l) (κ : ↥(GK K) →* (↥L.1)ˣ) (hκ : Continuous fun g => (κ g : ↥L.1)) (w : ℤ)
    (hw : Loc.HasWeight (GK K).subtype κ w) (hd : IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) : multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ a = if a = -w then 1 else 0 := by
  have := L.2
  have := K.2
  have : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  obtain ⟨T⟩ := Loc.tiedP l
  have hφ : Topology.IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  have h := (Loc.charFil (GK K).subtype hφ κ hκ w hw).2
  have hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL := ↥L.1) (V := ↥L.1) i := fun i => by
    have : (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] =
        (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l] := SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)
    unfold Loc.FilT FilV
    rw [this]
  have hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := by
    unfold Loc.Ddr DdR
    refine iInf_congr fun g => ?_
    have h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g := by
      unfold actVdR Loc.actD
      congr 1
      exact LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z
    rw [h2]
  simp only [Loc.FilD, hF, hD] at h
  have hr := (((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans
    (Module.finrank_self _)
  have hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := inf_le_left
  have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
    rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
  have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
    rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
  unfold multV
  rcases lt_trichotomy a (-w) with ha | ha | ha
  · rw [h1 a ha.le, h1 (a + 1) ha, if_neg ha.ne]; simp
  · rw [h1 a ha.le, h0 (a + 1) (by omega), if_pos ha]; simp
  · rw [h0 a ha, h0 (a + 1) (by omega), if_neg ha.ne']; simp
private theorem flag_mult (K L : FinExt l) (n : ℕ) : ∀ (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1))
    (M : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1) (κ : Fin n → ↥(GK K) →* (↥L.1)ˣ),
    (∀ g x, ρ g x = (M g).mulVec x) → (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
    IsDR ((Loc.PP l).PD K) ρ → (∀ i, IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i))) ∧
      ∀ τ a, multV ((Loc.PP l).PD K) ρ τ a = ∑ i, multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i)) τ a := by
  obtain ⟨T⟩ := Loc.tiedP l
  induction n with
  | zero =>
    intro ρ M κ _ _ _ _
    refine ⟨fun i => i.elim0, fun τ a => ?_⟩
    have : Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR) := inferInstance
    simp [multV, Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    intro ρ M κ hρ hM hκ hd
    let ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1) := LinearMap.single _ (fun _ => ↥L.1) 0
    let π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1) := LinearMap.funLeft _ _ Fin.succ
    let M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1 := fun g => (M g).submatrix Fin.succ Fin.succ
    have hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x) := fun g x => by
      funext i
      simp [π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hM g i.succ 0 (Fin.succ_pos i)]
    have hs : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    let ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1) :=
      { toFun := fun g => Matrix.toLin' (M' g)
        map_one' := LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Matrix.toLin'_apply, ← hπ, map_one]; rfl
        map_mul' := fun g h => LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ,
            map_mul]; rfl }
    obtain ⟨d0, d2, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π
      (fun g x => by
        funext i
        rw [hρ]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])
      hπ (fun x y h => by simpa [ι] using congrFun h 0) hs
      (by
        ext x
        simp only [LinearMap.mem_range, LinearMap.mem_ker]
        constructor
        · rintro ⟨y, rfl⟩
          funext i
          simp [ι, π, LinearMap.funLeft_apply]
        · intro h
          refine ⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩
          · simp [ι]
          · simpa [ι, π, LinearMap.funLeft_apply] using (congrFun h i).symm) hd
    obtain ⟨e1, e2⟩ := ih ρ' M' (fun i => κ i.succ) (fun g x => rfl)
      (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2
    refine ⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩
    rw [(hm τ a).2.1, Fin.sum_univ_succ, e2]
private theorem exists_open (K : FinExt l) {M : ℕ} (hM : 1 ≤ M) : ∃ U : Subgroup ↥(GK K), IsOpen (U : Set ↥(GK K)) ∧
    ∀ s ∈ U, ∀ ζ : Om l, ζ ^ M = 1 → (s : GQ l) ζ = ζ := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M
  have : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {z}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  refine ⟨(IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup.comap (GK K).subtype,
    (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val, fun s hs ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h : (s : GQ l) z = z := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
    (IntermediateField.mem_adjoin_simple_self _ z)
  rw [map_pow, h]
end UpperTheory.V.Af.JumpsAbove
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.JumpsAbove in
theorem UpperTheory.V.Af.jumps_above_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.JumpsAbove := by
  rintro - F Ω _ _ _ _ _ l _ - n M hM m r hr w A - O _ _ _ Bw hj κ ⟨χ, hχ, ⟨g, hg⟩, hI⟩ τ J hJ
  obtain ⟨L, r', hL, hd, τ', -, hc⟩ := (GlobalTheory.ConjLocal.local_conj l (Loc.PP l) F Ω O _ Bw n _
    ((MulAut.conj g).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)) g (fun _ => rfl)).2.2.2 τ J hJ
  have he : ∀ s i j, ((r' s i j : ↥L.1) : Om l) = (g * r s * g⁻¹ : GL (Fin n) (Om l)) i j := fun s i j =>
    congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin n) (Om l) => (f s : Matrix (Fin n) (Fin n) (Om l)) i j) hL.2
  have hκ : ∀ s i, ((r' s i i : ↥L.1) : Om l) = κ i s := fun s i => (he s i i).trans ((hg s).2 i)
  let κ' : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => r' (Bw.e.symm s) i i
      map_one' := by simp
      map_mul' := fun s t => Subtype.ext (by
        rw [IntermediateField.coe_mul, hκ, hκ, hκ, map_mul, map_mul, Units.val_mul]) }
  have hκ' : ∀ i s, ((κ' i s : ↥L.1) : Om l) = κ i (Bw.e.symm s) := fun i s => hκ _ _
  obtain ⟨d, hm⟩ := flag_mult Bw.Kw L n (Bw.repE L r') (fun s => r' (Bw.e.symm s)) κ' (fun _ _ => rfl)
    (fun s i j h => Subtype.ext ((he _ i j).trans ((hg _).1 i j h))) (fun _ _ => rfl)
    (by rw [IsDR, Module.finrank_fin_fun]; exact hd)
  obtain ⟨U, hU, hUζ⟩ := exists_open Bw.Kw hM
  have hcm : ∀ (s : ↥(GK Bw.Kw)) x, (s : GQ l) (Bw.j x) = Bw.j ((Bw.e.symm s : G F Ω) x) := fun s x => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  have key : ∀ i a, multV ((Loc.PP l).PD Bw.Kw) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ' i)) τ' a = if a = -m i then 1 else 0 := fun i a => by
    refine char_mult Bw.Kw L (κ' i) (continuous_induced_rng.2 ?_) (m i) ⟨U, hU, fun s hs hq => ?_⟩ (d i) τ' a
    · have h1 : Continuous fun s : ↥(GK Bw.Kw) => g * r (Bw.e.symm s) * g⁻¹ :=
        (continuous_const.mul (hr.comp (continuous_subtype_val.comp Bw.e_symm_cont))).mul continuous_const
      exact ((Units.continuous_val.comp h1).matrix_elem i i).congr fun s => (he _ i i).symm
    · have hine : (Bw.e.symm s : G F Ω) ∈ Ine (F := F) A := by
        refine ⟨(Bw.e.symm s).2, fun x hx => ?_⟩
        rw [hj.valuation_lt_one_iff, map_sub, ← hcm]
        exact ((Loc.iqBasic l).2.2.1 _).1 hq _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
      have h1 : χ i (Bw.e.symm s) = 1 := hχ i _ fun ζ hζ => Bw.j.injective (by
        rw [← hcm, hUζ s hs _ (by rw [← map_pow, hζ, map_one])])
      have h2 := (GlobalTheory.Survey.CrystallineCharacterRatio.chi_eq_cyc (Loc.PP l) Bw.j _ _ (hcm s)).symm.trans ((Loc.cycFacts l l).2.2 s)
      refine Units.ext (Subtype.ext ?_)
      rw [hκ', hI i _ hine, h1, mul_one, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
      refine Eq.trans ?_ (map_zpow₀ (algebraMap ↥L.1 (Om l)) _ _).symm
      congr 1
      exact congrArg (algebraMap ℚ_[l] (Om l)) h2
  ext a
  have h := hc a
  rw [LocBridge.multE, hm] at h
  simp only [key] at h
  rw [Multiset.count_map, ← Nat.cast_inj (R := ℤ), h]
  simp [Finset.card_def]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix
namespace UpperTheory.V.Af.GlobalFixedVectors
variable {F : Type} [Field F] [NumberField F] {n M : ℕ}
end UpperTheory.V.Af.GlobalFixedVectors
open UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.V.Af.globFixed_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.GlobFixed := by
  classical
  intro _ F _ _ n M _ V _ _ ρ hρ h
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), HasFixed ρ (KAway n M S) → HasFixed ρ (KAway n M ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hv0, hv⟩
      obtain ⟨σ, ⟨-, hσ⟩, hfix⟩ := h w
      let W : Submodule ℂ V := ⨅ k : KAway n M (insert w S), LinearMap.ker (ρ k - 1)
      have hWm : ∀ x, x ∈ W ↔ ∀ k ∈ KAway n M (insert w S), ρ k x = x := fun x => by
        simp [W, Submodule.mem_iInf, sub_eq_zero]
      obtain ⟨x, hxW, hx0, hx⟩ := sub_fixed σ.ρ σ.irred (ρ.comp (locGL F n w)) hσ W (fun g x hx => (hWm _).2 fun k hk => by
        have e : k * locGL F n w g = locGL F n w g * k := gl_ext fun u => by
          by_cases hu : u = w
          · subst hu; simp [(mem_KAway.1 hk).2 u (Finset.mem_insert_self _ _)]
          · simp [pLoc_locGL_of_ne hu]
        change ρ k (ρ (locGL F n w g) x) = ρ (locGL F n w g) x
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hWm x).1 hx k hk])
        (fun e => hv0 (by simpa [e] using (hWm v).2 hv)) _ hfix
      refine ih ⟨x, hx0, fun k hk => ?_⟩
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway n M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : ρ (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) x = x := hx _ h1
      have h4 := (hWm x).1 hxW _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨σ, ⟨hV, -⟩, -⟩ := h w
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) ((hρ v).mem_nhds (by simp))
  obtain ⟨x, hx0, hx⟩ := key S ⟨v, hv, fun k hk => hS hk⟩
  exact ⟨x, hx0, fun k hk => hx k (mem_KAway.2 ⟨hk, by simp⟩)⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Lev.fixed_semisimple_of_flag_fixed_dvd_fixed_unramified :
    UpperTheory.V.Lev.FlagPol → _root_.UpperTheory.V.Lev.FixedDvdAlt → _root_.UpperTheory.V.Lev.FixedUnrAlt → _root_.UpperTheory.V.Lev.FixedSsAlt := by
  intro hP hD hU F Ω _ _ _ _ _ l _ ι n M hM m r hr w A h O _ _ _ Bw hj κ hF hst rc hrc σ hc hor
  obtain ⟨μ, hμ, hI, hG⟩ := hP F Ω l ι n M hM m r hr w A h O Bw hj κ hF hst
  have hpol : ∀ s, (rc (GlobalTheory.GalOfCusp.algNorm σ)).charPol s = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
    rw [← hc ⟨μ, hμ⟩ s]
    exact hμ s
  by_cases hw : (M : 𝓞 F) ∈ w.asIdeal
  · refine hD F Ω n M hM w hw A h rc hrc σ fun s hs => ?_
    rw [hpol]
    simp [hI _ s hs]
  · have hin : ∀ i (s : ↥(Ine (F := F) A)), μ i (ineIncl h s) = 1 := fun i s =>
      hI i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char F Ω w A h M hw s s.2)
    obtain ⟨hiw, hsp⟩ := hU F Ω n w A h rc hrc σ μ hpol hin
    have hS : GlobalTheory.SmGL.IsSpherical σ.ρ := by
      rcases hor with ⟨k, rfl⟩ | hk | hs
      · exfalso
        have hlw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := hj.mem_placesOver h
        exact hw (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hlw)
      · refine hsp fun i j => ?_
        by_contra hne
        push_neg at hne
        rcases hG i j hne with e | e
        · exact hk i j e
        · exact hk j i e
      · exact hs hiw
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS
    exact ⟨v, hv0, fun u hu => by simpa using hv ⟨u, (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M u hu).1⟩⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Lev.fixedDvd_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedDvdAlt
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (Polynomial.X - 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
private theorem UpperTheory.V.Z.Win.T2.char_of_dvd {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ) (hM : 1 ≤ M) (x z : WD h)
    (hx : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      x.charPol (ineIncl h s) = (Polynomial.X - 1) ^ n)
    (hz : IsIrrWD z) (hd : ∀ σ, z.charPol σ ∣ x.charPol σ) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h2 := hd (ineIncl h s)
    rw [hx s hs, WD.charPol_mk] at h2
    exact UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩
private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2
private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩
theorem UpperTheory.V.Z.Win.T2.fixedDvd' :
    _root_.UpperTheory.V.Lev.fixedDvd_s_ty := by
  intro P F Ω _ _ _ _ _ n M hM w hw A h rc hrc σ hL
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  have hv : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := UpperTheory.V.Z.Win.T2.val_lt_one w hw
  have hM0 : (M : w.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (w.adicCompletion F)), map_ne_zero]
    exact Nat.cast_ne_zero.2 (by omega)
  have hu0 : uniformizer (w.adicCompletion F) ≠ 0 := by simp
  have hv0 : valuation (w.adicCompletion F) (M : w.adicCompletion F) ≠ 0 := by simpa using hM0
  let γ : (ValueGroupWithZero (w.adicCompletion F))ˣ :=
    Units.mk0 (valuation _ (M : w.adicCompletion F) / uniformizer (w.adicCompletion F)) (div_ne_zero hv0 hu0)
  have hlt : ∀ x : ValueGroupWithZero (w.adicCompletion F),
      x < γ ↔ x ≤ valuation _ (M : w.adicCompletion F) := fun x => by
    show x < _ / _ ↔ _
    rw [lt_div_iff₀ (zero_lt_iff.2 hu0)]
    refine ⟨fun h1 => not_lt.1 fun h2 => h1.not_ge ?_, fun h1 => (mul_le_mul_left h1 _).trans_lt
      (mul_lt_of_lt_one_right (zero_lt_iff.2 hv0) uniformizer_lt_one)⟩
    have hx : 0 < x := (zero_lt_iff.2 hv0).trans h2
    rwa [← div_le_iff₀' hx, le_uniformizer_iff, div_lt_one₀ hx]
  have hγ : γ ≤ 1 := by
    show _ / _ ≤ (1 : ValueGroupWithZero (w.adicCompletion F))
    rw [div_le_one₀ (zero_lt_iff.2 hu0), le_uniformizer_iff]
    exact hv
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport P.litN.loc.zel (algNorm σ)
  have hch : ∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : (w.adicCompletion F)ˣ,
      valuation (w.adicCompletion F) ((u : w.adicCompletion F) - 1) < γ → χ u = 1 := fun y hy => by
    obtain ⟨ξ, hξ, e, hξ1⟩ := UpperTheory.V.Z.Win.T2.char_of_dvd w A h M n hM _ (rc y) hL ((H.cusp y).1 (hs.isCusp hy)) fun τ => by
      rw [H.supp _ s hs τ]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol τ) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    refine ⟨χ, hχ, H.inj _ _ (UpperTheory.V.Z.Win.T2.good_ofChar χ hχ) (e.trans (H.one χ hχ).symm), fun u hu => ?_⟩
    obtain ⟨τ, rfl⟩ := ha.surj u
    have h1 : valuation (w.adicCompletion F) (a τ : w.adicCompletion F) = 1 := by
      have := (valuation (w.adicCompletion F)).map_one_add_of_lt (hu.trans_le (Units.val_le_val.2 hγ))
      simpa using this
    obtain ⟨h2, h3⟩ := UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence P.litN.aut.art F Ω w A h a ha M hM τ h1 ((hlt _).1 hu)
    exact hξ1 ⟨τ, h2⟩ h3
  have hne := UpperTheory.jacquet_borel_nontrivial_of_character_support P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s hs fun y hy => by
    obtain ⟨χ, hχ, rfl, -⟩ := hch y hy
    rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_borel_exists_torus_congruence_fixed P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s γ hγ hs hch hne
  have hf := UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed _ _ _ (algNorm σ).rep γ hγ
    ((P.litN.loc.bz _).1 _ _ _ (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr) y hy0 hy
  refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hf
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, fun i j => (hlt _).2 ((UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).2 i j)⟩, hv0⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
abbrev _root_.UpperTheory.V.Lev.fixedUnr_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedUnrAlt
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩
private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]
end
theorem UpperTheory.V.Z.Win.T2.fixedUnr_alt :
    _root_.UpperTheory.V.Lev.fixedUnr_s_ty := by
  intro P F Ω _ _ _ _ _ n w A h rc hrc σ μ hp hu
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hine : ∀ t : Ine (F := F) A, (rc (algNorm σ)).charPol (ineIncl h t) = (X - C 1) ^ n := fun t => by
    rw [hp]
    simp [hu]
  constructor
  · have hfx : fixed (algNorm σ).rep (iwahori (w.adicCompletion F) (Fin (algNorm σ).1)) ≠ ⊥ := by
      refine UnramSupport.fixed_iwahori_ne_bot P.litN.loc.geo P.litN.loc.zel P.litN.loc.bz _ _ _ _
        (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr fun s hs y hy => ?_
      have hyc : y.IsCusp := hs.isCusp hy
      obtain ⟨m, b, hb, hirr⟩ := id ((H.cusp y).1 hyc)
      have hN : b.N = 0 := by
        have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne F Ω A w h (rc y) ((H.cusp y).1 hyc)
        rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
      have hI : ∀ t : Ine (F := F) A, b.ρ (ineIncl h t) = 1 := fun t => by
        refine eq_one_of_dvd _ (b.semisimple _) (n := n) ?_
        rw [← WD.charPol_mk, hb, ← hine t, H.supp _ s hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol (ineIncl h t)) hy)
      have hunr : (rc y).unr := by
        rw [← hb, WD.unr_mk]
        exact ⟨hN, hI⟩
      exact isUnramChar_of_isCusp_of_isSpherical P.litN.loc.geo P.litN.loc.bz P.litN.loc.zel _ y hyc
        ((H.sph y).2 hunr)
    have hfx' : fixed (IrrGL.of σ.ρ σ.smooth σ.irred).rep (iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ :=
      GlobalTheory.AboveL.IwaFix.fixed_iwahori_ne_bot_of_twist _
        ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _)) hfx
    exact fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm hfx'
  · intro hne
    obtain ⟨m, b, hb⟩ := (rc (algNorm σ)).exists_rep
    have hpb : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
      rw [← WD.charPol_mk, hb]
      exact hp s
    have hN : b.N = 0 := by
      by_contra h0
      obtain ⟨i, j, e⟩ := link b μ hpb h0
      obtain ⟨s, hs⟩ := hne i j
      exact hs (link_all μ hu e s)
    have hunr : (rc (algNorm σ)).unr := by
      rw [← hb, WD.unr_mk]
      refine ⟨hN, fun t => eq_one_of_dvd _ (b.semisimple _) (n := n) ?_⟩
      rw [← WD.charPol_mk, hb, hine t]
    obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hunr)
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.Parabolic.mem_fixed.2 hv, hv0⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Lev.fixedSs_of_prints (P : _root_.UpperTheory.V.Af.Hypotheses') : _root_.UpperTheory.V.Lev.FixedSsAlt :=
  _root_.UpperTheory.V.Lev.fixed_semisimple_of_flag_fixed_dvd_fixed_unramified UpperTheory.V.Lev.flagPol (_root_.UpperTheory.V.Z.Win.T2.fixedDvd' P) (_root_.UpperTheory.V.Z.Win.T2.fixedUnr_alt P)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
private theorem UpperTheory.V.Af.isOpen_fixMu {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ}
    (hM : 1 ≤ M) : IsOpen {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M from hM)] using hζ
  have e : {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} =
      ⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) ζ : Set (Ω ≃ₐ[F] Ω)) := by
    ext s
    simp [MulAction.mem_stabilizer_iff]
  rw [e]
  exact hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ
theorem UpperTheory.V.Af.weil_deligne_away_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAway := by
  intro _ F Ω _ _ _ _ _ l _ ι n M hM r _ w hl A h χ hχ hd x hx
  obtain ⟨g, hg⟩ := hd
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open ((UpperTheory.V.Af.isOpen_fixMu (F := F) (Ω := Ω) hM).preimage continuous_subtype_val)
      (fun ζ _ => rfl) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ σ.2]
    simp [fun i => hχ i σ hσ]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), a, fun i s hs => ?_, rfl, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s s.2, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private infOf_of_weights not_mem_of_not_dvd from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelKO
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Keep
theorem levelCore_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (hn : 2 ≤ n) (m : Fin n → ℤ)
    (M : ℕ) (hM : 1 ≤ M) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (hL : LevelF l M m r)
    (hU : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → Unl1 r w ∨ PotUnl r w) (hW : WitA ι r)
    (hreg : (CG.mk π).IsRegAlg) (hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) (ha : AttC ι r π) :
    (∀ τ, π.HasInfChar τ (infOf m)) ∧ HasFixed π.finPart (KLev K n M) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B → FrobEig ι r w (algSat n (normV w) B) := by
  obtain ⟨HT, hwt, hC⟩ := compatT (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n (by omega) r π hL.cont hreg hpol ha
  have hw' : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w := fun w =>
    (em _).elim (fun e => Or.inr (hU w e)) Or.inl
  refine ⟨fun φ => ?_, ?_, fun w hw B hB => ?_⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
    have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
    have hJ := _root_.UpperTheory.V.Af.jumps_above_of_printed_results P K Ω l hl n M hM m r hL.cont w A hA O Bw hj κ hκ τ _
      (((hC w σ hσ).2 g.1 A hA O Bw hj).2 τ _ τ' hτ')
    have hw := hwt τ
    rw [hJ, hφ] at hw
    rw [← infOf_of_weights hw]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine _root_.UpperTheory.V.Af.globFixed_alt P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      obtain ⟨hp, he⟩ := ((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).2 O Bw hj g.2
      refine _root_.UpperTheory.V.Lev.fixedSs_of_prints P K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp rc hrc σ (fun _ s => by rw [he]) ?_
      by_cases hlM : l ∣ M
      · exact Or.inl hlM
      refine Or.inr (Or.inr fun _ => ?_)
      obtain ⟨μ, m1, m2, -⟩ := flagPol K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp
      refine sphV (_root_.UpperTheory.V.Z.Win.toV' hrc) σ g.2.2 n fun s => ?_
      rw [← he, m1]
      simp only [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M (not_mem_of_not_dvd hw hlM) s s.2), Units.val_one, C_1,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · obtain ⟨A, hA, χ, h1, h2⟩ := hL.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      exact _root_.UpperTheory.V.Z.Win.T2.local_fixed_vectors_statement P K Ω n M hM w A hA rc hrc σ
        (_root_.UpperTheory.V.Af.weil_deligne_away_of_printed_results P K Ω l ι n M hM r hL.cont w hw A hA χ h1 h2 _
          ((((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).1 hw).isWDOf g.2))
  · obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    exact _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P K Ω l ι n r hL.cont w hw σ B (((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => ((hC w σ hσ).1 A h rc hrc).1 hw
theorem levelPA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelPA := by
  intro K _ _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hs hW hreg hpol ha
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π hL (fun w hw => hs.elim (fun a => Or.inr (a.2 w hw)) fun hg => by
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    have hu := unlGap K Ω l n M hM m r w hw A hA κ hκ hg
    obtain ⟨χ, -, h2, -⟩ := hκ
    exact Or.inl (A4.unlOfOne K Ω l n r w A hA κ h2 hu)) hW hreg hpol ha
  exact ⟨⟨h.1, hpol, h.2.1⟩, h.2.2⟩
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : G F Ω →* GL (Fin n) (Qbar l)}
end
theorem levelKA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelKA := by
  intro K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hU hW hreg hd ha
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π (LevelF.of_level hL) hU hW hreg ⟨_, hpol⟩ ha
  exact ⟨⟨h.1, hd, h.2.1⟩, h.2.2⟩
end UpperTheory.V.Keep
end
end
end
