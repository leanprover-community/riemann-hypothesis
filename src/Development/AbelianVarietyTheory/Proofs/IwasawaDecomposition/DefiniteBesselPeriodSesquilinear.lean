import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousUnitaryRootExchangeMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselCoeffIndep

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ]

theorem haar_eq_of_covolume_one (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (h' : IsFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ'
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have h2 : IsFundamentalDomain Γ 𝓕 μ' := h.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h3 : μ' 𝓕 = 1 := (h2.measure_eq h').trans h1'
  rw [e, Measure.smul_apply, h1, smul_eq_mul, mul_one] at h3
  rw [e, h3, one_smul]

theorem setIntegral_mul_right (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [h2, one_smul] at e
  have hp : MeasurePreserving (· * g) μ μ := ⟨measurable_mul_const g, e⟩
  rw [← hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕]
  exact h.setIntegral_eq h' (f := fun x => f (x * g)) fun γ x => by
    show f ((γ : G) * x * g) = _
    rw [mul_assoc, hf _ γ.2]

end General

section Character

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hA_coeff hD_swap_zero co co_surj)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_act_e (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) {l i : Fin d.ρ} (h : l ≤ i) :
    hA B (actV B n (d.e l)) (vecA B (d.f i)) = if l = i then 1 else 0 := by
  obtain ⟨c, hc, e⟩ := hn.1 l
  rw [e, hA_add, hA_coeff B d.e d.f d.ef, hc i h, add_zero, hA_vec, d.ef]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem actE_eq_of_conj_related (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) (i : Fin d.ρ) :
    B.hD (d.aux i.succ) (d.f i) = 0 ∧ ∃ c : Fin d.ρ → AE D, (∀ l, i < l → c l = 0) ∧
      actV B n (d.aux i.succ) = vecA B (d.aux i.succ) + ∑ l, c l • vecA B (d.e l) := by
  unfold BesselDatum.aux
  by_cases hi : i.1 + 1 = d.ρ
  · have : i.succ = Fin.last d.ρ := Fin.ext hi
    rw [this, Fin.snoc_last]
    obtain ⟨c, e⟩ := hn.2 d.z fun j => hD_swap_zero (d.ez j)
    exact ⟨hD_swap_zero (d.fz i), c, fun l hl => absurd (show i.1 < l.1 from hl) (by have := l.2; omega), e⟩
  · have hlt : i.1 + 1 < d.ρ := by have := i.2; omega
    have : i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin d.ρ) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    obtain ⟨c, hc, e⟩ := hn.1 ⟨i.1 + 1, hlt⟩
    refine ⟨?_, c, fun l hl => hc l (show i.1 + 1 ≤ l.1 from hl), e⟩
    rw [d.ef, if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega)]

theorem simpleSum_mul (d : BesselDatum A B ι) {n n' : GA D B} (hn : n ∈ d.NSet) (hn' : n' ∈ d.NSet) :
    d.simpleSum (n * n') = d.simpleSum n + d.simpleSum n' := by
  unfold BesselDatum.simpleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h0, c, hc, e⟩ := actE_eq_of_conj_related d hn' i
  have e1 : actV B (n * n') (d.aux i.succ) = actV B n (d.aux i.succ) + ∑ l, c l • actV B n (d.e l) := by
    have : actV B (n * n') (d.aux i.succ) = (mt B n).mulVec (actV B n' (d.aux i.succ)) := mulVec_mul _ _ _
    rw [this, e, Matrix.mulVec_add, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rfl
  rw [e1, e, hA_add, hA_add, hA_coeff B d.e d.f d.ef, hA_vec, h0, RingHom.map_zero, zero_add, hA_sum,
    Finset.sum_eq_single i]
  · rw [hA_smul, hA_act_e d hn le_rfl, if_pos rfl, mul_one]
  · intro l _ hl
    rw [hA_smul]
    rcases lt_or_ge i l with h | h
    · rw [hc l h, zero_mul]
    · rw [hA_act_e d hn h, if_neg hl, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem psiN_mul (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {n n' : GA D B} (hn : n ∈ d.NSet)
    (hn' : n' ∈ d.NSet) : d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := by
  unfold BesselDatum.psiN
  rw [simpleSum_mul d hn hn', mul_add, LinearMap.map_add, AddChar.map_add_eq_mul]

theorem psiN_rat (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {n : GA D B}
    (hn : n ∈ GQ B) : d.psiN ψ n = 1 := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  have h1 : mt B n = (g : Matrix _ _ D.host.E).map (incA D) := (congrArg Units.val hg).symm
  have h2 : ∀ v, ∃ w, actV B n v = vecA B w := fun v => by
    obtain ⟨w, hw⟩ := co_surj B ((g : Matrix _ _ D.host.E).mulVec (co B v))
    refine ⟨w, funext fun k => ?_⟩
    have : vecA B w k = incA D (co B w k) := rfl
    rw [this, hw, RingHom.map_mulVec, actV, h1]
    rfl
  choose w hw using h2
  have h3 : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := fun e => by
    show Algebra.trace (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) (1 ⊗ₜ e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  unfold BesselDatum.psiN BesselDatum.simpleSum
  simp only [hw, hA_vec]
  rw [← map_sum (incA D), ← RingHom.map_mul, h3, hψ.2.2.1]

end Character

theorem coeff_indep_and_equivariant : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → (∀ ν' 𝓝', d.IsUnitPair ν' 𝓝' → d.coeff ψ ν' 𝓝' F = d.coeff ψ ν 𝓝 F) ∧ ∀ n ∈ d.N, ∀ g, d.coeff ψ ν 𝓝 F (n * g) = d.psiN ψ n * d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 ⟨hν, h𝓝, h1⟩
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hcl := (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).2
  have : LocallyCompactSpace d.N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace d.N := Subtype.borelSpace _
  have : Countable d.NQ :=
    Function.Injective.countable (f := fun γ : d.NQ => (⟨γ.1.1, γ.2⟩ : GQ B)) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun t : GQ B => (t : GA D B)) hab))
  have hS : ∀ n ∈ d.N, n ∈ d.NSet := fun n hn => (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).1 ▸ SetLike.mem_coe.2 hn
  have hmul : ∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := fun n hn n' hn' =>
    psiN_mul d ψ (hS n hn) (hS n' hn')
  have hrat : ∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1 := fun n _ hn' => psiN_rat d ψ hψ.1 hn'
  have hinv : ∀ g, ∀ γ ∈ d.NQ, ∀ x : d.N,
      F (((γ * x : d.N) : GA D B) * g) * star (d.psiN ψ ((γ * x : d.N) : GA D B)) =
        F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)) := fun g γ hγ x => by
    rw [Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ, hmul _ γ.2 _ x.2, hrat _ γ.2 hγ, one_mul]
  refine ⟨fun ν' 𝓝' ⟨hν', h𝓝', h1'⟩ => ?_, fun n hn g => ?_⟩
  · obtain rfl := haar_eq_of_covolume_one d.NQ ν ν' h𝓝 h𝓝' h1 h1'
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup d.NQ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup d.NQ ν'
    funext g
    exact h𝓝'.setIntegral_eq h𝓝 (f := fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)))
      fun γ x => hinv g γ γ.2 x
  · have key := setIntegral_mul_right d.NQ ν h𝓝 (by rw [h1]; exact ENNReal.one_ne_top)
      (fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) (hinv g) ⟨n, hn⟩
    unfold BesselDatum.coeff
    rw [← key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hu : d.psiN ψ n * star (d.psiN ψ n) = 1 := by
      have : ‖d.psiN ψ n‖ = 1 := hψ.1.2.1 _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]; simp
    simp only [Subgroup.coe_mul]
    rw [hmul _ x.2 _ hn, star_mul', mul_assoc (x : GA D B)]
    linear_combination (-(F (x * (n * g)) * star (d.psiN ψ x))) * hu

end GlobalTheory.Mem.BesselCoeffIndep
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffRational

theorem conj_closure {G : Type} [Group G] (S : Set G) (γ : G) (h : ∀ n ∈ S, γ * n * γ⁻¹ ∈ S) :
    ∀ n ∈ Subgroup.closure S, γ * n * γ⁻¹ ∈ Subgroup.closure S := by
  have : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj γ).toMonoidHom :=
    (Subgroup.closure_le _).2 fun n hn => Subgroup.subset_closure (h n hn)
  exact fun n hn => this hn

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjN (N : Subgroup G) (γ : G) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ⁻¹ * n * γ, h2 n n.2⟩
  invFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  left_inv n := Subtype.ext (by simp [mul_assoc])
  right_inv n := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem exists_pair [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G) (γ : G) (hγ : γ ∈ Q)
    (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ ∈ N) (ν : Measure N) (𝓝 : Set N)
    (hν : ν.IsHaarMeasure) (hF : IsFundamentalDomain (Q.subgroupOf N) 𝓝 ν) (hv : ν 𝓝 = 1) :
    ∃ (ν' : Measure N) (𝓝' : Set N), (ν'.IsHaarMeasure ∧ IsFundamentalDomain (Q.subgroupOf N) 𝓝' ν' ∧ ν' 𝓝' = 1) ∧
      ∀ f : G → ℂ, ∫ n in 𝓝', f n ∂ν' = ∫ n in 𝓝, f (γ⁻¹ * n * γ) ∂ν := by
  let c := conjN N γ h1 h2
  let cm : N ≃ᵐ N := c.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving cm ν (ν.map cm) := ⟨cm.measurable, rfl⟩
  have hpre : cm ⁻¹' (cm.symm ⁻¹' 𝓝) = 𝓝 := by
    ext x; simp
  refine ⟨ν.map cm, cm.symm ⁻¹' 𝓝, ⟨c.isHaarMeasure_map ν, ?_, ?_⟩, fun f => ?_⟩
  · let e : Q.subgroupOf N → Q.subgroupOf N := fun q =>
      ⟨c q.1, Subgroup.mem_subgroupOf.2 (Q.mul_mem (Q.mul_mem (Q.inv_mem hγ) (Subgroup.mem_subgroupOf.1 q.2)) hγ)⟩
    have he : Function.Bijective e := by
      refine ⟨fun a b h => Subtype.ext (c.injective (congrArg Subtype.val h)), fun q => ?_⟩
      exact ⟨⟨c.symm q.1, Subgroup.mem_subgroupOf.2
        (Q.mul_mem (Q.mul_mem hγ (Subgroup.mem_subgroupOf.1 q.2)) (Q.inv_mem hγ))⟩,
        Subtype.ext (c.apply_symm_apply _)⟩
    refine hF.preimage_of_equiv (hmp.symm cm).quasiMeasurePreserving he fun q x => ?_
    show c.symm (c q.1 * x) = q.1 * c.symm x
    rw [map_mul, c.symm_apply_apply]
  · rw [cm.map_apply, hpre, hv]
  · rw [setIntegral_map_equiv, hpre]
    rfl

end General

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem emb_fix {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    (mt B γ).mulVec (vecA B v) = vecA B v :=
  hγ.2 (co B v) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hv _)

theorem emb_iA {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) (t : Fin A.rank → AE D) :
    (mt B γ).mulVec (iA ι t) = iA ι ((mt A h).mulVec t) := by
  unfold iA
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M t) hγ.1

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_emb (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  funext k
  have h1 := RingHom.map_mulVec (incA D) (frameMat B A ι) (A.frame.repr a) k
  rw [frameMat, LinearMap.toMatrix_mulVec_repr] at h1
  exact h1

theorem emb_move (hι : HSpace.IsIsomEmb A B ι) {γ : GA D B} {h : GA D A} (hγ : EmbRel B A ι γ h) (x : B.V) :
    ∃ t, (mt B γ).mulVec (vecA B x) = vecA B x + iA ι t := by
  obtain ⟨a, ha⟩ := exists_rep A ((B.hT x).comp ι)
  have h1 : ∀ y, B.hD (x - ι a) (ι y) = 0 := fun y => hD_swap_zero (by
    show B.hT (x - ι a) (ι y) = 0
    rw [map_sub, LinearMap.sub_apply, hι a y, ha, LinearMap.comp_apply, sub_self])
  have h2 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a) := by
    rw [← vecA_emb, ← vecA_add, sub_add_cancel]
  refine ⟨(mt A h).mulVec (vecA A a) + -vecA A a, ?_⟩
  rw [h2, Matrix.mulVec_add, emb_fix hγ h1, emb_iA hγ, iA_add, iA_neg]
  abel

set_option maxHeartbeats 1000000 in
theorem conj_NSet (d : BesselDatum A B ι) {γ : GA D B} {h h' : GA D A} (hγ : EmbRel B A ι γ h)
    (hγ' : EmbRel B A ι γ⁻¹ h') {n : GA D B} (hn : n ∈ d.NSet) : γ * n * γ⁻¹ ∈ d.NSet := by
  have hsum : ∀ c : Fin d.ρ → AE D, (mt B γ).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l) := by
    intro c
    rw [← Matrix.mulVecLin_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Matrix.mulVecLin_apply, emb_fix hγ (d.eA l)]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, e⟩ := hn.1 i
    refine ⟨c, hc, ?_⟩
    unfold actV at e ⊢
    rw [mulVec_mul, mulVec_mul, emb_fix hγ' (d.eA i), e, Matrix.mulVec_add, emb_fix hγ (d.eA i), hsum]
  · obtain ⟨t, ht⟩ := emb_move d.isom hγ' x
    obtain ⟨c, e⟩ := hn.2 x hx
    choose a ha using fun k => hn.2 (ι (A.frame k)) fun i => hD_swap_zero (d.eA i _)
    unfold actV at e ha ⊢
    have e2 : (mt B n).mulVec (iA ι t) = iA ι t + ∑ l, (∑ k, t k * a k l) • vecA B (d.e l) := by
      rw [iA, frameMat_eq, eMat_mulVec, ← Matrix.mulVecLin_apply, map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply, ha, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    refine ⟨fun l => c l + ∑ k, t k * a k l, ?_⟩
    have e3 : (mt B n).mulVec ((mt B γ⁻¹).mulVec (vecA B x)) =
        (mt B γ⁻¹).mulVec (vecA B x) + ∑ l, (c l + ∑ k, t k * a k l) • vecA B (d.e l) := by
      rw [ht, Matrix.mulVec_add, e, e2]
      simp only [add_smul, Finset.sum_add_distrib]
      abel
    rw [mulVec_mul, mulVec_mul, e3, Matrix.mulVec_add]
    exact congrArg₂ (· + ·) (mulVec_cancel_inv γ (vecA B x)) (hsum fun l => c l + ∑ k, t k * a k l)

theorem conj_N (d : BesselDatum A B ι) {γ : GA D B} {h h' : GA D A} (hγ : EmbRel B A ι γ h)
    (hγ' : EmbRel B A ι γ⁻¹ h') : ∀ n ∈ d.N, γ * n * γ⁻¹ ∈ d.N := by
  have h1 : ∀ n ∈ d.NSet, γ * n * γ⁻¹ ∈ d.NSet := fun n hn => conj_NSet d hγ hγ' hn
  have h2 := conj_closure (G := GA D B) d.NSet γ h1
  unfold BesselDatum.N
  exact h2

theorem psiN_conj (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {γ : GA D B} {h : GA D A}
    (hγ : EmbRel B A ι γ h) (n : GA D B) : d.psiN ψ (γ⁻¹ * n * γ) = d.psiN ψ n := by
  unfold BesselDatum.psiN BesselDatum.simpleSum actV
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_mul, mulVec_mul, emb_fix hγ (besselDatum_auxiliaryVector_orthogonal_image d _), hA_mt_left, inv_inv, emb_fix hγ (d.fA i)]

end Conj

theorem coeff_rational : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ γ h, EmbRel B A ι γ h → γ ∈ GQ B → ∀ g, d.coeff ψ ν 𝓝 F (γ * g) = d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 hν γ h hγ hQ g
  haveI : BorelSpace (GA D B) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D B) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B).2.2.2.2.1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  have hγ' : EmbRel B A ι γ⁻¹ h⁻¹ := by
    rw [hs] at hγ ⊢
    rw [hγ, map_inv]
  have h1 := conj_N d hγ hγ'
  have h2 : ∀ n ∈ d.N, γ⁻¹ * n * γ ∈ d.N := fun n hn => by
    have := conj_N d hγ' (by rwa [inv_inv]) n hn
    rwa [inv_inv] at this
  obtain ⟨ν', 𝓝', hν', hint⟩ := exists_pair d.N (GQ B) γ hQ h1 h2 ν 𝓝 hν.1 hν.2.1 hν.2.2
  have e := congrFun ((GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF ν 𝓝 hν).1 ν' 𝓝' hν') g
  rw [← e]
  unfold BesselDatum.coeff
  rw [hint fun n => F (n * g) * star (d.psiN ψ n)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  show F (n * (γ * g)) * star (d.psiN ψ n) = F (γ⁻¹ * n * γ * g) * star (d.psiN ψ (γ⁻¹ * n * γ))
  rw [psiN_conj d ψ hγ, mul_assoc, mul_assoc, hF _ ((GQ B).inv_mem hQ)]

end GlobalTheory.CoeffRational

end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselDecomp

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hD_basis_dual (d : BesselDatum A B ι) (i l) : B.hD (d.aux l) (dual d i) = if l = i then 1 else 0 := by
  have hz : star (B.hT d.z d.z) = B.hT d.z d.z := (hT_swap rfl).symm
  have zz : B.hT d.z d.z ≠ 0 := d.zz
  unfold BesselDatum.aux dual
  refine Fin.lastCases ?_ (fun j => ?_) i <;> refine Fin.lastCases ?_ (fun k => ?_) l
  · simp [HSpace.hD, starRingEnd_apply, hz, zz]
  · have : B.hT d.z (d.e k) = 0 := d.ez k
    simp [HSpace.hD, this, Fin.castSucc_ne_last]
  · rw [Fin.snoc_last, Fin.snoc_castSucc, hD_swap_zero (d.fz j), if_neg (Fin.castSucc_ne_last j).symm]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, d.ef]
    simp

theorem f_dual (d : BesselDatum A B ι) (i l) : B.hD (d.f l) (dual d i) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have : B.hT d.z (d.f l) = 0 := d.fz l
    simp [HSpace.hD, this]
  · rw [Fin.snoc_castSucc, d.ff]

theorem hD_basis_e (d : BesselDatum A B ι) (i l) : B.hD (d.aux i) (d.e l) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, hD_swap_zero (d.ez l)]
  · rw [Fin.snoc_castSucc, d.ee]

theorem f_e (d : BesselDatum A B ι) (k l) : B.hD (d.f k) (d.e l) = if k = l then 1 else 0 := by
  have h : B.hT (d.e l) (d.f k) = star (if l = k then 1 else 0) := hT_swap (d.ef l k)
  unfold HSpace.hD
  rw [h]
  by_cases e : k = l
  · simp [e]
  · simp [e, Ne.symm e]

def comb (d : BesselDatum A B ι) :
    (A.V × (Fin (d.ρ + 1) → D.host.E) × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
  ι.coprod ((Fintype.linearCombination D.host.E d.aux).coprod (Fintype.linearCombination D.host.E d.f))

theorem comb_inj (d : BesselDatum A B ι) : Function.Injective (comb d) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s, r⟩ h
  simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
  have h1 : ∀ i l, B.hT (dual d i) (d.aux l) = if l = i then 1 else 0 := hD_basis_dual d
  have h2 : ∀ i l, B.hT (dual d i) (d.f l) = 0 := f_dual d
  have h3 : ∀ i l, B.hT (d.e l) (d.aux i) = 0 := hD_basis_e d
  have h4 : ∀ k l, B.hT (d.e l) (d.f k) = if k = l then 1 else 0 := f_e d
  have h5 : ∀ i, B.hT (dual d i) (ι a) = 0 := fun i => hD_swap_zero (dual_perp d i a)
  have h6 : ∀ l, B.hT (d.e l) (ι a) = 0 := fun l => hD_swap_zero (d.eA l a)
  have hs : s = 0 := by
    funext i
    simpa [map_sum, h1, h2, h5] using congrArg (B.hT (dual d i)) h
  have hr : r = 0 := by
    funext l
    simpa [map_sum, h3, h4, h6] using congrArg (B.hT (d.e l)) h
  subst hs hr
  have ha : ι a = 0 := by simpa using h
  have : a = 0 := by
    refine A.nondeg.1 a fun y => ?_
    rw [← d.isom a y, ha]; simp
  subst this
  rfl

theorem comb_surj (d : BesselDatum A B ι) : Function.Surjective (comb d) := by
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (comb_inj d)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, A.rank_eq, B.rank_eq,
    d.rank_eq]
  omega

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {n : ℕ} (c : Fin n → D.host.E) (v : Fin n → B.V) :
    vecA B (∑ i, c i • v i) = ∑ i, incA D (c i) • vecA B (v i) := by
  funext k; simp [vecA, map_sum, Finset.sum_apply]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  conv_lhs => rw [← A.frame.sum_repr a, map_sum]
  simp only [map_smul]
  rw [vecA_sum]
  rfl

theorem exists_comb (d : BesselDatum A B ι) (x : Fin B.rank → AE D) :
    ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      x = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l) := by
  have hx : x = ∑ k, x k • vecA B (B.frame k) := by
    funext j
    simp [vecA, Finset.sum_apply, Finsupp.single_apply, apply_ite (incA D)]
  rw [hx]
  refine Finset.sum_induction _ (fun y => ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      y = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l)) ?_ ?_ ?_
  · rintro _ _ ⟨t, s, r, rfl⟩ ⟨t', s', r', rfl⟩
    refine ⟨t + t', s + s', r + r', ?_⟩
    simp only [iA_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  · exact ⟨0, 0, 0, by simp [iA]⟩
  · intro k _
    obtain ⟨⟨a, s, r⟩, h⟩ := comb_surj d (B.frame k)
    simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
    refine ⟨x k • vecA A a, fun i => x k * incA D (s i), fun l => x k * incA D (r l), ?_⟩
    rw [← h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota, iA_smul]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_assoc]

theorem iA_vec {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (iA ι t) (vecA B v) = 0 := by
  rw [← hA_herm, hA_vec_iA h, map_zero]

theorem decomp : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧
    ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) +
      ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  intro D A B ι d
  refine ⟨hD_basis_dual d, f_dual d, fun x => ?_⟩
  obtain ⟨t, s, r, h⟩ := exists_comb d x
  have hs : ∀ i, hA B x (vecA B (dual d i)) = s i := fun i => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (dual_perp d i)]
    simp [hA_smul, hA_vec, hD_basis_dual, f_dual, apply_ite (incA D)]
  have hr : ∀ l, hA B x (vecA B (d.e l)) = r l := fun l => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (d.eA l)]
    simp [hA_smul, hA_vec, hD_basis_e, f_e, apply_ite (incA D)]
  exact ⟨t, by simp only [hs, hr]; exact h⟩

end GlobalTheory.BesselDecomp

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDatum_adelicVector_decomposition : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧ ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) + ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  atlas_forward_decl GlobalTheory.BesselDecomp.decomp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitaryRootExchangeMap : ∀ (D : D7) (B : HSp D) (η : AE D), η * cA D η = 0 → ∀ v : Fin B.rank → AE D, ∃ K : {y : Fin B.rank → AE D // η • y = y ∧ hA B v y = 0} → GA D B, Continuous K ∧ ∀ y, IsK B v y.1 (K y) := by
  first | exact @GlobalTheory.RootUnip.exists_continuous_isK | exact GlobalTheory.RootUnip.exists_continuous_isK | (intros; apply GlobalTheory.RootUnip.exists_continuous_isK <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.ExStruct

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_half {ε : AE D} {y : Fin B.rank → AE D} (hy : ε • y = y) (x) : hA B x y = cA D ε * hA B x y := by
  rw [← hA_smul_right, hy]

theorem eps_hA {ε : AE D} (h0 : ε * cA D ε = 0) {y : Fin B.rank → AE D} (hy : ε • y = y) (x) :
    ε * hA B x y = 0 := by
  rw [hA_half hy, ← mul_assoc, h0, zero_mul]

theorem hA_smul_zero {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (x) : hA B x y' • y = 0 := by
  rw [← hy, smul_smul, mul_comm, eps_hA h0 hy', zero_smul]

theorem hA_halves {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') : hA B y y' = 0 := by
  rw [← hy, hA_smul, eps_hA h0 hy']

theorem isK_mul {ε : AE D} (h0 : ε * cA D ε = 0) {v y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (hv' : hA B y' v = 0) (hv : hA B v y = 0) {k k' : GA D B} (hk : IsK B v y k)
    (hk' : IsK B v y' k') : IsK B v (y + y') (k * k') := by
  intro x
  rw [mulVec_mul, hk', hk]
  simp only [hA_add, hA_sub, hA_smul, hA_add_right, hv, hv', hA_halves h0 hy' hy, mul_zero, add_zero, sub_zero,
    add_smul, smul_add, mul_comm (hA B x y'), mul_smul, hA_smul_zero h0 hy hy', smul_zero, zero_smul]
  abel

theorem isK_eps {ε : AE D} (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y) {k : GA D B}
    (hk : IsK B v y k) (x) : ε • ((mt B k).mulVec x - x) = -(hA B x v • y) := by
  rw [hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, eps_hA h0 hy, zero_smul, zero_sub, smul_comm, hy]

theorem isK_supp {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y)
    {k : GA D B} (hk : IsK B v y k) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have hc : cA D ε • y = 0 := by rw [← hy, smul_smul, mul_comm, h0, zero_smul]
  rw [add_smul, isK_eps h0 hy hk, hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, ← hA_half hy,
    smul_comm, hc, smul_zero]
  abel

theorem eq_one_of_half {ε : AE D} {u : GA D B} (hu : SuppAt ε B u) (h : ∀ x, ε • ((mt B u).mulVec x - x) = 0) :
    u = 1 := by
  refine mt_ext fun x => ?_
  rw [mt_one, Matrix.one_mulVec, ← sub_eq_zero, ← suppAt_iff_vec.1 hu x, add_smul, h, zero_add]
  refine hA_nondeg fun y => ?_
  have e : (mt B u).mulVec (ε • y) = ε • y := by
    have := h y
    rwa [smul_sub, sub_eq_zero, ← Matrix.mulVec_smul] at this
  rw [hA_smul, ← hA_smul_right, hA_sub]
  conv_lhs => rw [← e]
  rw [hA_mt, e, sub_self]

theorem iA_eq (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]

theorem dual_iA (d : BesselDatum A B ι) (i) (t) : hA B (vecA B (dual d i)) (iA ι t) = 0 :=
  hA_vec_iA (dual_perp d i) t

theorem iA_dual (d : BesselDatum A B ι) (i) (t) : hA B (iA ι t) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, dual_iA, map_zero]

theorem vec_dual (d : BesselDatum A B ι) (i) (x : A.V) : hA B (vecA B (ι x)) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, hA_vec, dual_perp, map_zero, map_zero]

theorem mem_exSet (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t)
    {k : GA D B} (hk : IsK B (vecA B (dual d i)) (iA ι t) k) :
    SuppAt ε B k ∧
    (∀ x : A.V, ε • (actV B k (ι x) - vecA B (ι x)) = 0) ∧
    (∀ l, ε • (actV B k (d.f l) - vecA B (d.f l)) = 0) ∧
    (∀ l, l ≠ i → ε • (actV B k (d.aux l) - vecA B (d.aux l)) = 0) ∧
      ε • (actV B k (d.aux i) - vecA B (d.aux i)) = -iA ι t := by
  have hy : ε • iA ι t = iA ι t := by rw [← iA_smul, ht]
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d
  unfold actV
  refine ⟨isK_supp h1 h0 hy hk, fun x => ?_, fun l => ?_, fun l hl => ?_, ?_⟩
  · rw [isK_eps h0 hy hk, vec_dual, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p2, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_neg hl, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_pos rfl, map_one, one_smul]

theorem exists_k (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t) :
    ∃ k : GA D B, IsK B (vecA B (dual d i)) (iA ι t) k := by
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.exists_continuous_unitaryRootExchangeMap D B ε h0 (vecA B (dual d i))
  exact ⟨_, hK ⟨iA ι t, by rw [← iA_smul, ht], dual_iA d i t⟩⟩

theorem isK_one (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => (h x).trans (h' x).symm

def kGrp (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) where
  carrier := {g | ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g}
  one_mem' := ⟨0, smul_zero _, by rw [iA, Matrix.mulVec_zero]; exact isK_one _⟩
  mul_mem' := by
    rintro g g' ⟨t, ht, hg⟩ ⟨t', ht', hg'⟩
    refine ⟨t + t', by rw [smul_add, ht, ht'], ?_⟩
    rw [iA_add]
    exact isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hg'
  inv_mem' := by
    rintro g ⟨t, ht, hg⟩
    have ht' : ε • (-t) = -t := by rw [smul_neg, ht]
    obtain ⟨k, hk⟩ := exists_k d h0 i ht'
    have := isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hk
    rw [iA_neg, add_neg_cancel] at this
    rw [inv_eq_of_mul_eq_one_right (isK_unique this (isK_one _))]
    exact ⟨-t, ht', hk⟩

theorem mulVec_comb (L : Matrix (Fin B.rank) (Fin B.rank) (AE D)) {a : ℕ} (u : Fin a → Fin B.rank → AE D)
    (hu : ∀ i, L.mulVec (u i) = 0) (r : Fin a → AE D) : L.mulVec (∑ i, r i • u i) = 0 := by
  refine Finset.sum_induction _ (fun x => L.mulVec x = 0) (fun x y hx hy => ?_) (Matrix.mulVec_zero _) fun i _ => ?_
  · rw [Matrix.mulVec_add, hx, hy, add_zero]
  · rw [Matrix.mulVec_smul, hu, smul_zero]

theorem mulVec_zero_of (d : BesselDatum A B ι) (L : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0) (a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0)
    (a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0) (x) : L.mulVec x = 0 := by
  obtain ⟨t, e⟩ := (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).2.2 x
  rw [e, iA_eq, Matrix.mulVec_add, Matrix.mulVec_add, mulVec_comb L _ (fun l => a1 (A.frame l)),
    mulVec_comb L _ a3, mulVec_comb L _ a2, add_zero, add_zero]

theorem eq_of_half {ε : AE D} {g k : GA D B} (g1 : SuppAt ε B g) (k1 : SuppAt ε B k)
    (h : ∀ x, ε • ((mt B g).mulVec x - x) = ε • ((mt B k).mulVec x - x)) : k = g := by
  refine inv_mul_eq_one.1 (eq_one_of_half (suppAt_mul (suppAt_inv k1) g1) fun x => ?_)
  have e : ε • (mt B g).mulVec x = ε • (mt B k).mulVec x := by
    have := h x
    rwa [smul_sub, smul_sub, sub_left_inj] at this
  have := congrArg (mt B k⁻¹).mulVec e
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_inv_cancel, ← mulVec_mul] at this
  rw [smul_sub, this, sub_self]

set_option maxHeartbeats 800000 in
theorem exSet_sub (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {g : GA D B}
    (hg : g ∈ d.ExSet ε i) : g ∈ kGrp d h0 i := by
  obtain ⟨g1, g2, g3, g4, y, g5⟩ := hg
  have ht : ε • (-(ε • y)) = -(ε • y) := by rw [smul_neg, smul_smul, h1]
  obtain ⟨k, hk⟩ := exists_k d h0 i ht
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin B.rank) (Fin B.rank) (AE D),
      ∀ x, L.mulVec x = ε • ((mt B g).mulVec x - x) - ε • ((mt B k).mulVec x - x) :=
    ⟨ε • (mt B g - mt B k), fun x => by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← Matrix.sub_mulVec, ← Matrix.smul_mulVec]⟩
  have a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0 := fun x => by
    rw [hL]; exact sub_eq_zero.2 ((g2 x).trans (k2 x).symm)
  have a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0 := fun l => by
    rw [hL]; exact sub_eq_zero.2 ((g3 l).trans (k3 l).symm)
  have a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0 := fun l => by
    rw [hL]
    by_cases hl : l = i
    · subst hl
      refine sub_eq_zero.2 (g5.trans (Eq.symm (k5.trans ?_)))
      rw [iA_neg, neg_neg, iA_smul]; rfl
    · exact sub_eq_zero.2 ((g4 l hl).trans (k4 l hl).symm)
  have a4 : ∀ x, L.mulVec x = 0 := mulVec_zero_of d L a1 a2 a3
  rw [← eq_of_half g1 k1 fun x => sub_eq_zero.1 ((hL x).symm.trans (a4 x))]
  exact ⟨_, ht, hk⟩

theorem mem_Ex_iff : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  intro D A B ι d ε he i g
  have h1 : ε * ε = ε := he.1
  have h0 : ε * cA D ε = 0 := he.2.1
  refine ⟨fun hg => (Subgroup.closure_le (kGrp d h0 i)).2 (fun _ h => exSet_sub d h1 h0 i h) hg, ?_⟩
  rintro ⟨t, ht, hk⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  refine Subgroup.subset_closure ⟨k1, k2, k3, k4, -t, k5.trans ?_⟩
  show _ = ε • iA ι (-t)
  rw [← iA_smul, smul_neg, ht, iA_neg]

end GlobalTheory.RootExch.ExStruct

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  first | exact @GlobalTheory.RootExch.ExStruct.mem_Ex_iff | exact GlobalTheory.RootExch.ExStruct.mem_Ex_iff | (intros; apply GlobalTheory.RootExch.ExStruct.mem_Ex_iff <;> assumption)
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.Mirror

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem suppAt_of_isK {ε a : AE D} {v y : Fin B.rank → AE D} {k : GA D B} (hk : IsK B v y k) (hy : a • y = y)
    (h1 : (ε + cA D ε) * a = a) (h2 : (ε + cA D ε) * cA D a = cA D a) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have e1 : (ε + cA D ε) * hA B x y = hA B x y := by
    rw [← hy, hA_smul_right, ← mul_assoc, h2]
  have e2 : (ε + cA D ε) • y = y := by
    conv_lhs => rw [← hy]
    rw [smul_smul, h1, hy]
  have e : (mt B k).mulVec x - x = hA B x y • v - hA B x v • y := by rw [hk x]; abel
  rw [e, smul_sub, smul_smul, e1, smul_comm, e2]

def fixGrp (B : HSp D) (x : Fin B.rank → AE D) : Subgroup (GA D B) where
  carrier := {g | (mt B g).mulVec x = x}
  one_mem' := by show _ = _; rw [mt_one, Matrix.one_mulVec]
  mul_mem' := fun {g h} hg hh => by
    show _ = _
    rw [mulVec_mul, show (mt B h).mulVec x = x from hh, show (mt B g).mulVec x = x from hg]
  inv_mem' := fun {g} hg => by
    show _ = _
    conv_lhs => rw [← show (mt B g).mulVec x = x from hg]
    rw [mulVec_inv_cancel]

theorem fix_of_isK (d : BesselDatum A B ι) {i l : Fin (d.ρ + 1)} (h : l ≠ i) {t} {g : GA D B}
    (hg : IsK B (vecA B (dual d i)) (iA ι t) g) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  show _ = _
  rw [hg, hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d l), hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_neg h]
  simp

theorem fix_of_ExGe (d : BesselDatum A B ι) {ε : AE D} (he : IsSplitIdem D ε) {p : ℕ} {l : Fin (d.ρ + 1)} (h : l.1 < p)
    {g : GA D B} (hg : g ∈ ExGe d ε p) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  refine (Subgroup.closure_le _).2 (Set.iUnion_subset fun i => Set.iUnion_subset fun hi u hu => ?_) hg
  obtain ⟨t, -, ht⟩ := (GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange D A B ι d ε he i u).1 (Subgroup.subset_closure hu)
  exact fix_of_isK d (fun e => by rw [e] at h; omega) ht

theorem basis_castSucc (d : BesselDatum A B ι) (l : Fin d.ρ) : d.aux l.castSucc = d.e l := by
  unfold BesselDatum.aux; rw [Fin.snoc_castSucc]

theorem hD_basis_e (d : BesselDatum A B ι) (m) (j : Fin d.ρ) : B.hD (d.aux m) (d.e j) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun l => ?_) m
  · rw [Fin.snoc_last]; exact hD_swap_zero (d.ez j)
  · rw [Fin.snoc_castSucc]; exact d.ee l j

theorem hD_basis_succ_f (d : BesselDatum A B ι) (i : Fin d.ρ) : B.hD (d.aux i.succ) (d.f i) = 0 := by
  have key : ∀ m : Fin (d.ρ + 1), m.1 = i.1 + 1 → B.hD (d.aux m) (d.f i) = 0 := by
    intro m
    unfold BesselDatum.aux
    refine Fin.lastCases (fun _ => ?_) (fun l hl => ?_) m
    · rw [Fin.snoc_last]; exact hD_swap_zero (d.fz i)
    · rw [Fin.snoc_castSucc, d.ef, if_neg]
      rintro rfl
      simp at hl
  exact key _ rfl

theorem conj_apply {v y : Fin B.rank → AE D} {k c : GA D B} (hk : IsK B v y k) (hc : c ∈ fixGrp B v)
    {x : Fin B.rank → AE D} (hx : hA B x v = 0) :
    (mt B (c * k * c⁻¹)).mulVec x = x + hA B ((mt B c⁻¹).mulVec x) y • v := by
  have hc' : (mt B c).mulVec v = v := hc
  have h0 : hA B ((mt B c⁻¹).mulVec x) v = 0 := by rw [hA_mt_left, inv_inv, hc', hx]
  rw [mulVec_mul, mulVec_mul, hk, h0, zero_smul, sub_zero, Matrix.mulVec_add, Matrix.mulVec_smul, hc', mulVec_cancel_inv]

theorem sum_single (d : BesselDatum A B ι) (j : Fin d.ρ) (a : AE D) :
    ∑ l, (if l = j then a else 0) • vecA B (d.e l) = a • vecA B (d.e j) := by
  simp [ite_smul]

theorem mirror : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  intro D A B ι d ψ ε he j t₀ t b₀ k ht₀ ht hb₀ hk
  have h1 : ε * ε = ε := he.1
  have h2 : ε * cA D ε = 0 := he.2.1
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  have a1 : (ε + cA D ε) * ε = ε := by rw [add_mul, h1, mul_comm, h2, add_zero]
  have a2 : (ε + cA D ε) * cA D ε = cA D ε := by rw [add_mul, h2, h3, zero_add]
  have sk : SuppAt ε B k := suppAt_of_isK (a := cA D ε) hk (by rw [← iA_smul, ht]) a2 (by rw [cA_cA, a1])
  have sb : SuppAt ε B b₀ := suppAt_of_isK (a := ε) hb₀ (by rw [← iA_smul, ht₀]) a1 a2
  refine ⟨sk, fun b hb => ?_⟩
  have sb' := suppAt_of_mem_ExGe hb
  have hn : b * (b₀ * k * b₀⁻¹) * b⁻¹ = (b * b₀) * k * (b * b₀)⁻¹ := by group
  have hfix : ∀ l : Fin d.ρ, l ≤ j → b * b₀ ∈ fixGrp B (vecA B (d.e l)) := by
    intro l hl
    have hl' : l.1 ≤ j.1 := hl
    rw [← basis_castSucc]
    refine mul_mem (fix_of_ExGe d he (by simp; omega) hb) (fix_of_isK d (fun e => ?_) hb₀)
    have := congrArg Fin.val e
    simp at this; omega
  have hact : ∀ x : B.V, B.hD x (d.e j) = 0 → actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) x =
      vecA B x + hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B x)) (iA ι t) • vecA B (d.e j) := by
    intro x hx
    rw [hn]
    exact conj_apply hk (hfix j le_rfl) (by rw [hA_vec, hx, map_zero])
  refine ⟨Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩,
    suppAt_mul (suppAt_mul sb' (suppAt_mul (suppAt_mul sb sk) (suppAt_inv sb))) (suppAt_inv sb'), ?_⟩
  · refine ⟨_, fun l hl => ?_, by rw [hact _ (d.ee i j), ← sum_single]⟩
    split_ifs with h
    · subst h
      rw [show (mt B (b * b₀)⁻¹).mulVec (vecA B (d.e i)) = _ from inv_mem (hfix i hl), hA_vec_iA (d.eA i)]
    · rfl
  · exact ⟨_, by rw [hact _ (hx j), ← sum_single]⟩
  · unfold BesselDatum.psiN BesselDatum.simpleSum
    congr 3
    have e : ∀ i : Fin d.ρ, hA B (actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) (d.aux i.succ)) (vecA B (d.f i)) =
        if j = i then hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B (d.aux i.succ))) (iA ι t) else 0 := by
      intro i
      rw [hact _ (hD_basis_e d _ j), hA_add, hA_smul, hA_vec, hA_vec, hD_basis_succ_f, d.ef]
      split_ifs <;> simp
    simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hb' : (mt B b⁻¹).mulVec (vecA B (d.aux j.succ)) = vecA B (d.aux j.succ) :=
      inv_mem (fix_of_ExGe d he (by simp) hb)
    have p1 : hA B (iA ι t) (vecA B (dual d j.succ)) = 0 := by
      rw [← hA_herm, hA_vec_iA (dual_perp d _), map_zero]
    rw [_root_.mul_inv_rev, mulVec_mul, hb', hA_mt_left, inv_inv, hb₀, p1, zero_smul, sub_zero, hA_add_right,
      hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d _), zero_add, hA_smul_right, hA_herm, hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_pos rfl,
      map_one, mul_one, hA_iA d.isom]

end GlobalTheory.RootExch.Mirror

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRootExchange_mirror_identity : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  atlas_forward_decl GlobalTheory.RootExch.Mirror.mirror
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  first | exact @GlobalTheory.StdCharLocal.psiV_ne_one | exact GlobalTheory.StdCharLocal.psiV_ne_one | (intros; apply GlobalTheory.StdCharLocal.psiV_ne_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_annihilator_relativelyCompact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  first | exact @GlobalTheory.SplitAnnihilator.annihilator_subset_compact | exact GlobalTheory.SplitAnnihilator.annihilator_subset_compact | (intros; apply GlobalTheory.SplitAnnihilator.annihilator_subset_compact <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosLinVec

theorem hA_single {D : D7} (A : HSp D) (x : Fin A.rank → AE D) (i : Fin A.rank) (s : AE D) :
    hA A x (Pi.single i (cA D s)) = (A.gram.map (incA D)).mulVec x i * s := by
  rw [hA_eq, show (fun j => cA D ((Pi.single i (cA D s) : Fin A.rank → AE D) j)) = Pi.single i s from
    funext fun j => by by_cases e : j = i <;> simp [e, GlobalTheory.RootExch.cA_cA], single_dotProduct, mul_comm]

theorem vec_of_scalar {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (c : R →+* R) (hc : Continuous c) (ε u w : R) (huw : w * u = 1) (J : Matrix (Fin n) (Fin n) R) (hJ : IsUnit J)
    (h : (Fin n → R) → (Fin n → R) → R) (hh : ∀ x i s, h x (Pi.single i (c s)) = J.mulVec x i * s)
    (P : R → Prop)
    (H : ∀ V ∈ nhds (0 : R), ∃ C : Set R, IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → P (a * s)) → a ∈ C) :
    ∀ V ∈ nhds (0 : Fin n → R), ∃ C : Set (Fin n → R), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ →
      (∀ t ∈ V, c ε • t = t → P (u * h t₀ t)) → t₀ ∈ C := by
  intro V hV
  have hc' : ∀ i : Fin n, Continuous fun s : R => (Pi.single i (c s) : Fin n → R) := fun i =>
    (continuous_single (A := fun _ : Fin n => R) i).comp hc
  have hVi : ∀ i : Fin n, (fun s : R => (Pi.single i (c s) : Fin n → R)) ⁻¹' V ∈ nhds (0 : R) := fun i =>
    (hc' i).continuousAt.preimage_mem_nhds (by simpa only [map_zero, Pi.single_zero] using hV)
  choose C hC hmem using fun i => H _ (hVi i)
  obtain ⟨K, hK⟩ := hJ.exists_left_inv
  let g : (Fin n → R) → (Fin n → R) := fun a => w • K.mulVec a
  have hg0 : Continuous fun a : Fin n → R => K.mulVec a := continuous_const.matrix_mulVec continuous_id
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp hg0)
  refine ⟨g '' Set.pi Set.univ C, (isCompact_univ_pi hC).image hg, fun t₀ ht h' => ?_⟩
  refine ⟨u • J.mulVec t₀, fun i _ => hmem i _ ?_ fun s hs hεs => ?_, ?_⟩
  · conv_rhs => rw [← ht]
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · have := h' _ hs (by rw [← Pi.single_smul, smul_eq_mul, ← map_mul, hεs])
    rw [hh] at this
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact this
  · simp only [g]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hK, Matrix.one_mulVec, smul_smul, huw, one_smul]

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ (A : HSp D) (θ : D.host.E), θ ≠ 0 → ∀ V ∈ nhds (0 : Fin A.rank → AE D), ∃ C : Set (Fin A.rank → AE D), IsCompact C ∧ ∀ t₀, ε • t₀ = t₀ → (∀ t ∈ V, cA D ε • t = t → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D θ * hA A t₀ t)) = 1) → t₀ ∈ C := by
  intro D ψ hψ ε hε A θ hθ
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact vec_of_scalar (cA D) GlobalTheory.FockCompare.ThetaCont.continuous_conj ε (incA D θ) (incA D θ⁻¹)
    (by rw [← RingHom.map_mul, inv_mul_cancel₀ hθ, RingHom.map_one]) (A.gram.map (incA D))
    ((GlobalTheory.BesselCompare.gram_isUnit A).map (incA D).mapMatrix) (hA A) (hA_single A)
    (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1)
    (GlobalTheory.T.splitPlace_annihilator_relativelyCompact D ψ (GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one D ψ hψ) ε hε)

end GlobalTheory.PosLinVec
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.PosLinear

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def exL (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (l : List (Fin (d.ρ + 1)))
    (β : GA D B → ℂ) : GA D B → ℂ := l.foldr (fun i β' => exF d ε i (m i) β') β

def moveL (P : PosDatum A B ι) (l : List (Fin P.n)) (β : GA D B → ℂ) : GA D B → ℂ :=
  l.foldr (fun a β' => toPosF P.bes (P.ε a) (P.m a) (P.p a) β') β

theorem lvl_exL (d : BesselDatum A B ι) (ε : AE D) (m) (l) {β : GA D B → ℂ} (h : Lvl β) : Lvl (exL d ε m l β) := by
  obtain ⟨U, hU, hk⟩ := h
  refine ⟨U, hU, fun k k1 k2 => ?_⟩
  induction l with
  | nil => exact hk k k1 k2
  | cons i l ih =>
    intro g
    show ∫ u, exL d ε m l β ((u : GA D B) * (g * k)) ∂(m i) = ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    simp only [← mul_assoc, ih]

theorem eqv_exL (d : BesselDatum A B ι) (ψ) {ε ε' : AE D} (hε : (ε' + cA D ε') * (ε + cA D ε) = 0) (m) (l)
    {β : GA D B → ℂ} (h : Eqv d ψ ε' β) : Eqv d ψ ε' (exL d ε m l β) := by
  intro n hn hs
  induction l with
  | nil => exact h n hn hs
  | cons i l ih =>
    intro g
    show ∫ u, exL d ε m l β ((u : GA D B) * (n * g)) ∂(m i) = _ * ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show exL d ε m l β ((u : GA D B) * (n * g)) = _ * exL d ε m l β ((u : GA D B) * g)
    rw [← mul_assoc, ← commute_of_apart hε hs (suppAt_of_mem_Ex u.2), mul_assoc, ih]

theorem exL_left (d : BesselDatum A B ι) (ψ) (ε : AE D) (m) {β : GA D B → ℂ} (h : Eqv d ψ ε β) (p : ℕ) (c : ℂ)
    (l : List (Fin (d.ρ + 1))) (hl : ∀ i ∈ l, p ≤ i.1) :
    ∀ n, (∀ b ∈ ExGe d ε p, b * n * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * n * b⁻¹) ∧ d.psiN ψ (b * n * b⁻¹) = c) →
      ∀ g, exL d ε m l β (n * g) = c * exL d ε m l β g := by
  induction l with
  | nil =>
    intro n hn g
    have := hn 1 (one_mem _)
    simp only [one_mul, inv_one, mul_one] at this
    rw [← this.2.2]
    exact h n this.1 this.2.1 g
  | cons i l ih =>
    intro n hn g
    show ∫ u, exL d ε m l β ((u : GA D B) * (n * g)) ∂(m i) = _ * ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show exL d ε m l β ((u : GA D B) * (n * g)) = _ * exL d ε m l β ((u : GA D B) * g)
    have hu : (u : GA D B) ∈ ExGe d ε p := Ex_le_ExGe d ε (hl i List.mem_cons_self) u.2
    have e : (u : GA D B) * (n * g) = (u * n * (u : GA D B)⁻¹) * (u * g) := by
      simp only [mul_assoc, inv_mul_cancel_left]
    rw [e]
    refine ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ (fun b hb => ?_) _
    have e2 : b * (u * n * (u : GA D B)⁻¹) * b⁻¹ = (b * u) * n * (b * u)⁻¹ := by
      simp only [mul_assoc, _root_.mul_inv_rev]
    rw [e2]
    exact hn _ (mul_mem hb hu)

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => by rw [h x, h' x]

theorem isK_zero (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [GlobalTheory.BesselCompare.mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem continuous_iA : Continuous (iA (A := A) (B := B) ι) := by
  haveI : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  unfold iA
  exact continuous_const.matrix_mulVec continuous_id

theorem exists_K (η : AE D) (hη : η * cA D η = 0) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    ∃ K : {t : Fin A.rank → AE D // η • t = t} → GA D B, Continuous K ∧ ∀ t, IsK B (vecA B v) (iA ι t.1) (K t) := by
  obtain ⟨K, hK, hk⟩ := GlobalTheory.RootUnip.exists_continuous_isK D B η hη (vecA B v)
  refine ⟨fun t => K ⟨iA ι t.1, by rw [← iA_smul, t.2], hA_vec_iA hv _⟩,
    hK.comp (Continuous.subtype_mk (continuous_iA.comp continuous_subtype_val) _), fun t => hk _⟩

theorem isLocallyConstant_of_lvl {β : GA D B → ℂ} (h : Lvl β) (H : Subgroup (GA D B)) (hH : H ≤ GfC B) (g : GA D B) :
    IsLocallyConstant fun u : H => β ((u : GA D B) * g) := by
  haveI : IsTopologicalGroup (GA D B) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B).2.2.2.2.1
  obtain ⟨U, hU, hk⟩ := h
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨(fun u' : H => g⁻¹ * ((u : GA D B)⁻¹ * u') * g) ⁻¹' U, hU.preimage (by fun_prop), by simp, fun u' hu' => ?_⟩
  have hn : (GfC B).Normal := MonoidHom.normal_ker _
  have := hk _ hu' (hn.conj_mem' _ (hH (u⁻¹ * u').2) g) (u * g)
  rw [← this]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem exch_finite (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) {ε : AE D} (hε : IsSplitIdem D ε) (m)
    {β : GA D B → ℂ} (h1 : Lvl β) (h2 : Eqv d ψ ε β) (i : Fin (d.ρ + 1)) (hi : 1 ≤ i.1)
    (l : List (Fin (d.ρ + 1))) (hl : ∀ j ∈ l, i.1 + 1 ≤ j.1) (g : GA D B) :
    IsLocallyConstant (fun u : d.Ex ε i => exL d ε m l β ((u : GA D B) * g)) ∧
      HasCompactSupport (fun u : d.Ex ε i => exL d ε m l β ((u : GA D B) * g)) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  have hL := lvl_exL d ε m l h1
  refine ⟨isLocallyConstant_of_lvl hL _ (fun u hu => mem_GfC hε (suppAt_of_mem_Ex hu)) g, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : Fin d.ρ, i = j.succ := (Fin.eq_zero_or_eq_succ i).resolve_left (by rintro rfl; simp at hi)
  obtain ⟨U, hU, hk⟩ := hL
  obtain ⟨K, hK, hKk⟩ := exists_K (ι := ι) (cA D ε) (by rw [cA_cA, mul_comm, hε.2.1]) (d.eA j)
  obtain ⟨K₀, hK₀, hK₀k⟩ := exists_K (ι := ι) ε hε.2.1 (dual_perp d j.succ)
  have hmem : ∀ t, K₀ t ∈ d.Ex ε j.succ := fun t =>
    (GlobalTheory.RootExch.ExStruct.mem_Ex_iff D A B ι d ε hε _ _).2 ⟨t.1, t.2, hK₀k t⟩
  have hopen : IsOpen ((fun t => g⁻¹ * K t * g) ⁻¹' (U : Set (GA D B))) := hU.preimage (by fun_prop)
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1 hopen
  have h0 : (0 : Fin A.rank → AE D) ∈ V := by
    have : (⟨0, smul_zero _⟩ : {t : Fin A.rank → AE D // cA D ε • t = t}) ∈ Subtype.val ⁻¹' V := by
      rw [hVe]
      have e : K ⟨0, smul_zero _⟩ = 1 := isK_unique (hKk _) (by
        have : iA (A := A) (B := B) ι 0 = 0 := Matrix.mulVec_zero _
        rw [this]; exact isK_zero _)
      simp [e]
    exact this
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.PosLinVec.annihilator_subset_compact D ψ hψ ε hε A d.θ d.θ_ne V (hV.mem_nhds h0)
  have hcl : IsClosed {t : Fin A.rank → AE D | ε • t = t} := isClosed_eq (continuous_const_smul ε) continuous_id
  have hC' : IsCompact ((Subtype.val : {t : Fin A.rank → AE D // ε • t = t} → _) ⁻¹' C) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  refine HasCompactSupport.intro (hC'.image (f := fun t => (⟨K₀ t, hmem t⟩ : d.Ex ε j.succ))
    (hK₀.subtype_mk _)) fun u hu => ?_
  by_contra hne
  obtain ⟨t₀, ht₀, hu₀⟩ := (GlobalTheory.RootExch.ExStruct.mem_Ex_iff D A B ι d ε hε _ _).1 u.2
  refine hu ⟨⟨t₀, ht₀⟩, hCm t₀ ht₀ fun t htV ht => ?_, Subtype.ext (isK_unique (hK₀k _) hu₀)⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.T.unitaryRootExchange_mirror_identity D A B ι d ψ ε hε j t₀ t u (K ⟨t, ht⟩) ht₀ ht hu₀ (hKk _)
  have e1 := exL_left d ψ ε m h2 (j.1 + 2) _ l hl _ k2 (u * g)
  have hn : (GfC B).Normal := MonoidHom.normal_ker _
  have hU' : g⁻¹ * K ⟨t, ht⟩ * g ∈ U := by
    have : (⟨t, ht⟩ : {t : Fin A.rank → AE D // cA D ε • t = t}) ∈ Subtype.val ⁻¹' V := htV
    rw [hVe] at this
    exact this
  have e2 := hk _ hU' (hn.conj_mem' _ (mem_GfC hε k1) g) (u * g)
  have e3 : (u : GA D B) * g * (g⁻¹ * K ⟨t, ht⟩ * g) = u * K ⟨t, ht⟩ * (u : GA D B)⁻¹ * (u * g) := by
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  rw [e3, e1] at e2
  exact mul_right_cancel₀ hne (e2.trans (one_mul _).symm)

theorem exL_smul (d : BesselDatum A B ι) (ε : AE D) (m) (l) (c : ℂ) (β : GA D B → ℂ) :
    exL d ε m l (c • β) = c • exL d ε m l β := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext g
    show ∫ u, exL d ε m l (c • β) ((u : GA D B) * g) ∂(m i) = c * ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i)
    rw [ih, ← integral_const_mul]
    rfl

theorem exL_add (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) {ε : AE D} (hε : IsSplitIdem D ε) (m)
    (hm : ∀ i, (m i).IsHaarMeasure) {β β' : GA D B → ℂ} (h1 : Lvl β) (h2 : Eqv d ψ ε β) (h1' : Lvl β')
    (h2' : Eqv d ψ ε β') (l : List (Fin (d.ρ + 1))) (hl : ∀ j ∈ l, 1 ≤ j.1) (hs : l.Pairwise (· < ·)) :
    exL d ε m l (β + β') = exL d ε m l β + exL d ε m l β' := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext g
    show ∫ u, exL d ε m l (β + β') ((u : GA D B) * g) ∂(m i) =
      ∫ u, exL d ε m l β ((u : GA D B) * g) ∂(m i) + ∫ u, exL d ε m l β' ((u : GA D B) * g) ∂(m i)
    have hi := hl i List.mem_cons_self
    have hj : ∀ j ∈ l, i.1 + 1 ≤ j.1 := fun j hj => (List.pairwise_cons.1 hs).1 j hj
    obtain ⟨a1, a2⟩ := exch_finite d hψ hε m h1 h2 i hi l hj g
    obtain ⟨b1, b2⟩ := exch_finite d hψ hε m h1' h2' i hi l hj g
    haveI := hm i
    rw [ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) (List.pairwise_cons.1 hs).2,
      ← integral_add (a1.continuous.integrable_of_hasCompactSupport a2) (b1.continuous.integrable_of_hasCompactSupport b2)]
    rfl

theorem lvl_moveL (P : PosDatum A B ι) (l) {β : GA D B → ℂ} (h : Lvl β) : Lvl (moveL P l β) := by
  induction l with
  | nil => exact h
  | cons a l ih => exact lvl_exL P.bes (P.ε a) (P.m a) _ ih

theorem eqv_moveL (P : PosDatum A B ι) (ψ) {ε : AE D} (l : List (Fin P.n))
    (hl : ∀ a ∈ l, (ε + cA D ε) * (P.ε a + cA D (P.ε a)) = 0) {β : GA D B → ℂ} (h : Eqv P.bes ψ ε β) :
    Eqv P.bes ψ ε (moveL P l β) := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    exact eqv_exL P.bes ψ (hl a List.mem_cons_self) (P.m a) _ (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))

theorem moveL_smul (P : PosDatum A B ι) (l) (c : ℂ) (β : GA D B → ℂ) : moveL P l (c • β) = c • moveL P l β := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l (c • β)) = c • toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l β)
    rw [ih]
    exact exL_smul P.bes (P.ε a) (P.m a) _ c _

theorem moveL_add (P : PosDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) {β β' : GA D B → ℂ} (h1 : Lvl β)
    (h2 : ∀ ε, Eqv P.bes ψ ε β) (h1' : Lvl β') (h2' : ∀ ε, Eqv P.bes ψ ε β') (l : List (Fin P.n)) (hl : l.Nodup) :
    moveL P l (β + β') = moveL P l β + moveL P l β' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l (β + β')) =
      toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l β) + toPosF P.bes (P.ε a) (P.m a) (P.p a) (moveL P l β')
    obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
    have hap : ∀ b ∈ l, (P.ε a + cA D (P.ε a)) * (P.ε b + cA D (P.ε b)) = 0 := fun b hb =>
      P.apart a b fun e => ha (e ▸ hb)
    rw [ih hl']
    refine exL_add P.bes hψ (P.split a) (P.m a) (P.haar a) (lvl_moveL P l h1) (eqv_moveL P ψ l hap (h2 _))
      (lvl_moveL P l h1') (eqv_moveL P ψ l hap (h2' _)) _ (fun j hj => ?_) ((List.pairwise_lt_finRange _).filter _)
    exact (P.one_le a).trans (of_decide_eq_true (List.mem_filter.1 hj).2)

def perF (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure d.N) (𝓝 : Set d.N) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : GA D B → ℂ :=
  fun g => d.period ψ μ 𝓕 ν 𝓝 s φ (rTr B g F)

theorem coeff_rTr (d : BesselDatum A B ι) (ψ ν 𝓝) (F : GA D B → ℂ) (g x : GA D B) :
    d.coeff ψ ν 𝓝 (rTr B g F) x = d.coeff ψ ν 𝓝 F (x * g) := by
  simp only [BesselDatum.coeff, rTr, mul_assoc]

theorem perF_apply (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) (F : GA D B → ℂ) (g) :
    perF d ψ μ 𝓕 ν 𝓝 s φ F g = ∫ h in 𝓕, φ h * d.coeff ψ ν 𝓝 F (s h * g) ∂μ := by
  simp only [perF, BesselDatum.period, coeff_rTr]

theorem period_eq (P : PosDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) (F : GA D B → ℂ) :
    (fun g => P.period ψ μ 𝓕 ν 𝓝 s φ (rTr B g F)) = moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F) :=
  move_rTr P _ F

theorem period_eq' (P : PosDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) (F : GA D B → ℂ) :
    P.period ψ μ 𝓕 ν 𝓝 s φ F = moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F) 1 := by
  rw [← period_eq]
  simp only [rTr_one]

theorem lvl_perF (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ) {F : GA D B → ℂ} (hF : IsAutFun B F) :
    Lvl (perF d ψ μ 𝓕 ν 𝓝 s φ F) := by
  obtain ⟨U, hU, hk⟩ := hF.level
  refine ⟨U, hU, fun k k1 k2 g => ?_⟩
  have : rTr B (g * k) F = rTr B g F := funext fun x => by simp only [rTr, ← mul_assoc, hk k k1 k2]
  simp only [perF, this]

theorem eqv_perF (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) (μ 𝓕) {ν 𝓝} (hν : d.IsUnitPair ν 𝓝) {s}
    (hs : ∀ h, EmbRel B A ι (s h) h) (φ) {F : GA D B → ℂ} (hF : IsAutFun B F) (ε) :
    Eqv d ψ ε (perF d ψ μ 𝓕 ν 𝓝 s φ F) := by
  intro n hn _ g
  rw [perF_apply, perF_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  show φ h * d.coeff ψ ν 𝓝 F (s h * (n * g)) = _ * (φ h * d.coeff ψ ν 𝓝 F (s h * g))
  have e : s h * (n * g) = (s h * n * (s h)⁻¹) * (s h * g) := by simp only [mul_assoc, inv_mul_cancel_left]
  have e2 := GlobalTheory.CoeffRational.psiN_conj d ψ (hs h) (s h * n * (s h)⁻¹)
  have e3 : (s h)⁻¹ * (s h * n * (s h)⁻¹) * s h = n := by group
  rw [e3] at e2
  rw [e, (GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF.left ν 𝓝 hν).2 _
    (GlobalTheory.BesselConvDefinite.conj_mem_N d (hs h) hn), ← e2]
  ring

theorem exchangeFinite (D : D7) : ExchangeFinite D := by
  intro A B ι P ψ hψ _ μ 𝓕 _ ν 𝓝 hν s hs φ F _ hF _ ε hε hap m _ i hi
  have e : (fun u : P.bes.Ex ε i => P.bes.toPos ε m (i.1 + 1) (P.period ψ μ 𝓕 ν 𝓝 s φ) (rTr B (u : GA D B) F)) =
      fun u : P.bes.Ex ε i => exL P.bes ε m ((List.finRange (P.bes.ρ + 1)).filter fun j => decide (i.1 + 1 ≤ j.1))
        (moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F)) ((u : GA D B) * 1) := by
    funext u
    rw [mul_one, ← period_eq]
    exact congrFun (toPos_rTr P.bes ε m (i.1 + 1) _ F) u
  rw [e]
  exact exch_finite P.bes hψ hε m (lvl_moveL P _ (lvl_perF _ _ _ _ _ _ _ _ hF))
    (eqv_moveL P ψ _ (fun a _ => hap a) (eqv_perF _ hψ μ 𝓕 hν hs φ hF ε)) i hi _
    (fun j hj => of_decide_eq_true (List.mem_filter.1 hj).2) 1

theorem isAutFun_star {φ : GA D A → ℂ} (h : IsAutFun A φ) : IsAutFun A fun g => star (φ g) := by
  obtain ⟨U, hU, hk⟩ := h.level
  exact ⟨fun γ hγ g => by rw [h.left γ hγ], ⟨U, hU, fun k k1 k2 g => by rw [hk k k1 k2]⟩, h.cont.star⟩

theorem perF_indep (d : BesselDatum A B ι) {ψ} (hψ : IsStdChar D ψ (-1)) (hA : A.SigOK) {μ 𝓕 μ' 𝓕'}
    (hμ : IsVolPair D A μ 𝓕) (hμ' : IsVolPair D A μ' 𝓕') {ν 𝓝 ν' 𝓝'} (hν : d.IsUnitPair ν 𝓝)
    (hν' : d.IsUnitPair ν' 𝓝') {s s'} (hs : ∀ h, EmbRel B A ι (s h) h) (hs' : ∀ h, EmbRel B A ι (s' h) h)
    {φ F} (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    perF d ψ μ' 𝓕' ν' 𝓝' s' φ F = perF d ψ μ 𝓕 ν 𝓝 s φ F := by
  obtain ⟨s₀, -, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  obtain rfl : s' = s₀ := funext fun h => (hrel h _).1 (hs' h)
  obtain rfl : μ' = μ := (GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D A hA).unique hμ'.1 hμ.1
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  have := hμ.1.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ A)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ A) μ'
  funext g
  rw [perF_apply, perF_apply,
    (GlobalTheory.Mem.BesselCoeffIndep.coeff_indep_and_equivariant D A B ι d ψ hψ F hF.left ν 𝓝 hν).1 ν' 𝓝' hν']
  refine hμ'.2.setIntegral_eq hμ.2 fun γ x => ?_
  show φ (γ.1 * x) * d.coeff ψ ν 𝓝 F (s₀ (γ.1 * x) * g) = _
  rw [hφ.left _ γ.2, map_mul, mul_assoc,
    GlobalTheory.CoeffRational.coeff_rational D A B ι d ψ hψ F hF.left ν 𝓝 hν _ _ (hs γ.1) (hQ _ γ.2)]

theorem perF_smul_left (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s) (c : ℂ) (φ : GA D A → ℂ) (F : GA D B → ℂ) :
    perF d ψ μ 𝓕 ν 𝓝 s (c • φ) F = c • perF d ψ μ 𝓕 ν 𝓝 s φ F := by
  funext g
  simp only [perF_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem perF_smul_right (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s) (c : ℂ) (φ : GA D A → ℂ) (F : GA D B → ℂ) :
    perF d ψ μ 𝓕 ν 𝓝 s φ (c • F) = c • perF d ψ μ 𝓕 ν 𝓝 s φ F := by
  funext g
  have e : ∀ x, d.coeff ψ ν 𝓝 (c • F) x = c * d.coeff ψ ν 𝓝 F x := fun x => by
    simp only [BesselDatum.coeff, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  simp only [perF_apply, e, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

theorem perF_add_left (d : BesselDatum A B ι) {ψ μ 𝓕 ν 𝓝 s} {φ φ' : GA D A → ℂ} {F : GA D B → ℂ}
    (h : d.Converges ψ μ 𝓕 ν 𝓝 s φ F) (h' : d.Converges ψ μ 𝓕 ν 𝓝 s φ' F) :
    perF d ψ μ 𝓕 ν 𝓝 s (φ + φ') F = perF d ψ μ 𝓕 ν 𝓝 s φ F + perF d ψ μ 𝓕 ν 𝓝 s φ' F := by
  funext g
  simp only [perF, BesselDatum.period, Pi.add_apply, add_mul]
  exact integral_add (h g) (h' g)

theorem perF_add_right (d : BesselDatum A B ι) {ψ} (hψ : IsCharAF D.host.F ψ) {μ 𝓕 ν 𝓝 s} (hν : d.IsUnitPair ν 𝓝)
    {φ : GA D A → ℂ} {F F' : GA D B → ℂ} (hF : IsAutFun B F) (hF' : IsAutFun B F')
    (h : d.Converges ψ μ 𝓕 ν 𝓝 s φ F) (h' : d.Converges ψ μ 𝓕 ν 𝓝 s φ F') :
    perF d ψ μ 𝓕 ν 𝓝 s φ (F + F') = perF d ψ μ 𝓕 ν 𝓝 s φ F + perF d ψ μ 𝓕 ν 𝓝 s φ F' := by
  funext g
  have e : ∀ x, d.coeff ψ ν 𝓝 (F + F') x = d.coeff ψ ν 𝓝 F x + d.coeff ψ ν 𝓝 F' x := fun x => by
    simp only [BesselDatum.coeff, Pi.add_apply, add_mul]
    exact integral_add
      ((GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν F hF.cont hF.left).1 x)
      ((GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν F' hF'.cont hF'.left).1 x)
  have k := h g
  have k' := h' g
  simp only [coeff_rTr] at k k'
  simp only [perF_apply, e, Pi.add_apply, mul_add]
  exact integral_add k k'

theorem posLin : ∀ D : D7, PosLin D := by
  intro D
  refine ⟨GlobalTheory.BesselConvDefinite.convergesDef D, exchangeFinite D, fun θ hθ ψ hψ A B ι P hA hd => ?_⟩
  by_cases hex : ∃ μ 𝓕 ν 𝓝, ∃ s : GA D A → GA D B, IsVolPair D A μ 𝓕 ∧ P.bes.IsUnitPair ν 𝓝 ∧ ∀ h, EmbRel B A ι (s h) h
  swap
  · exact ⟨0, fun μ 𝓕 hμ ν 𝓝 hν s hs => absurd ⟨μ, 𝓕, ν, 𝓝, s, hμ, hν, hs⟩ hex⟩
  obtain ⟨μ, 𝓕, ν, 𝓝, s, hμ, hν, hs⟩ := hex
  have a1 : ∀ φ : AFs θ A, IsAutFun A fun g => star (φ.1 g) := fun φ =>
    isAutFun_star ((GlobalTheory.Mem.AutSpace.mem_AFs_iff D θ hθ A φ.1).1 φ.2).toIsAutFun
  have a2 : ∀ F : CuspS θ B, IsAutFun B F.1 := fun F =>
    ((GlobalTheory.Mem.AutSpace.mem_AFs_iff D θ hθ B F.1).1 (CuspS_le θ B F.2)).toIsAutFun
  have cv : ∀ (φ : AFs θ A) (F : CuspS θ B), P.bes.Converges ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1 := fun φ F =>
    GlobalTheory.BesselConvDefinite.convergesDef D A B ι P.bes ψ hψ.1 hA hd μ 𝓕 hμ ν 𝓝 hν s hs _ _ (a1 φ) (a2 F)
  have ad : ∀ φ φ' (F F' : CuspS θ B), moveL P (List.finRange P.n)
      (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F.1 + perF P.bes ψ μ 𝓕 ν 𝓝 s φ' F'.1) =
      moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ F.1) +
        moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s φ' F'.1) := fun φ φ' F F' =>
    moveL_add P hψ (lvl_perF _ _ _ _ _ _ _ _ (a2 F)) (eqv_perF _ hψ μ 𝓕 hν hs φ (a2 F))
      (lvl_perF _ _ _ _ _ _ _ _ (a2 F')) (eqv_perF _ hψ μ 𝓕 hν hs φ' (a2 F')) _ (List.nodup_finRange _)
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun (φ : AFs θ A) (F : CuspS θ B) =>
      moveL P (List.finRange P.n) (perF P.bes ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1) 1)
    (fun φ φ' F => ?_) (fun c φ F => ?_) (fun φ F F' => ?_) (fun c φ F => ?_),
    fun μ' 𝓕' hμ' ν' 𝓝' hν' s' hs' φ F => ?_⟩
  · have e : (fun g => star ((φ + φ').1 g)) = (fun g => star (φ.1 g)) + fun g => star (φ'.1 g) :=
      funext fun g => star_add _ _
    rw [e, perF_add_left _ (cv φ F) (cv φ' F), ad]
    rfl
  · have e : (fun g => star ((c • φ).1 g)) = starRingEnd ℂ c • fun g => star (φ.1 g) :=
      funext fun g => star_mul' _ _
    rw [e, perF_smul_left, moveL_smul]
    rfl
  · rw [Submodule.coe_add, perF_add_right _ hψ.1 hν (a2 F) (a2 F') (cv φ F) (cv φ F'), ad]
    rfl
  · rw [Submodule.coe_smul, perF_smul_right, moveL_smul]
    rfl
  · rw [period_eq', perF_indep P.bes hψ hA hμ hμ' hν hν' hs hs' (a1 φ) (a2 F)]
    rfl

end GlobalTheory.RootExch.PosLinear

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBesselPeriod_sesquilinear : ∀ D : D7, PosLin D := by
  atlas_forward_decl GlobalTheory.RootExch.PosLinear.posLin
end
