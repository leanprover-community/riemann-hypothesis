import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormula
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelic
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNorms
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogIdealEqLogAbsNorm
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFinite
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormulaStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData

section
noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

section Local

variable {L : Type} [Field L] [NumberField L]

theorem exists_max_det {n : ℕ} (E : Submodule (𝓞 L) (Fin n → 𝓞 L)) (hD : detIdeal E ≠ ⊥) (p : Nat.Primes)
    (j : L →+* ℂ_[p]) :
    ∃ (v : Fin n → Fin n → 𝓞 L) (u : 𝓞 L), (∀ i, v i ∈ E) ∧ (Matrix.of v).det ≠ 0 ∧
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E) = Real.log ‖j (((Matrix.of v).det : 𝓞 L) : L)‖ ∧
      ‖j (u : L)‖ = 1 ∧ ∀ w ∈ E, ∃ t : Fin n → 𝓞 L, u • w = ∑ k, t k • v k := by
  classical
  have hj'inj : Function.Injective (j.comp (algebraMap (𝓞 L) L)) :=
    j.injective.comp (IsFractionRing.injective (𝓞 L) L)
  obtain ⟨V, -, hV, hVO, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring L p j
  have hle1 : ∀ r : 𝓞 L, ‖(j.comp (algebraMap (𝓞 L) L)) r‖ ≤ 1 := fun r => (hV _).2 (hVO r)
  obtain ⟨a, haI, ha0, hamax, hlog⟩ := GlobalTheory.T.padic_logIdeal_max_element L p _ (detIdeal E) hj'inj hD
  have hapos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) a‖ :=
    norm_pos_iff.2 (fun h => ha0 (hj'inj (by rw [h, map_zero])))
  obtain ⟨v, hvE, hv⟩ : ∃ v : Fin n → Fin n → 𝓞 L, (∀ i, v i ∈ E) ∧
      ‖(j.comp (algebraMap (𝓞 L) L)) a‖ ≤ ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ x ∈ detIdeal E, ‖(j.comp (algebraMap (𝓞 L) L)) x‖ < ‖(j.comp (algebraMap (𝓞 L) L)) a‖ := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        exact hcon v hv
      | zero => simpa using hapos
      | add x y _ _ hx hy =>
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hle1 r)) hx
    exact lt_irrefl _ (hall a haI)
  have hdI : (Matrix.of v).det ∈ detIdeal E := det_mem_detIdeal E v hvE
  have hdeq : ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ = ‖(j.comp (algebraMap (𝓞 L) L)) a‖ :=
    le_antisymm (hamax _ hdI) hv
  have hd0 : (Matrix.of v).det ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hdeq
    linarith
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hdI)
  have hspan0 : Ideal.span {(Matrix.of v).det} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hspan0 hJ
  obtain ⟨hmul, hsing, -⟩ := GlobalTheory.T.log_ideal_mul_span_map L p _ hj'inj
  have hJlog : logIdeal (j.comp (algebraMap (𝓞 L) L)) J = 0 := by
    have := hmul _ J hD hJ0
    rw [← hJ, hsing, hdeq, hlog] at this
    linarith
  obtain ⟨u, huJ, hu0, -, hulog⟩ := GlobalTheory.T.padic_logIdeal_max_element L p _ J hj'inj hJ0
  have hu1 : ‖(j.comp (algebraMap (𝓞 L) L)) u‖ = 1 := by
    have hpos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) u‖ :=
      norm_pos_iff.2 (fun h => hu0 (hj'inj (by rw [h, map_zero])))
    rw [hJlog] at hulog
    rw [← Real.exp_log hpos, ← hulog, Real.exp_zero]
  refine ⟨v, u, hvE, hd0, ?_, hu1, ?_⟩
  · rw [hlog, ← hdeq]
    rfl
  · intro w hw
    have hc : ∀ k, u * (Matrix.of (Function.update v k w)).det ∈ Ideal.span {(Matrix.of v).det} := by
      intro k
      rw [hJ, mul_comm u]
      refine Ideal.mul_mem_mul (det_mem_detIdeal E _ fun i => ?_) huJ
      by_cases h : i = k
      · subst h
        simpa using hw
      · simpa [h] using hvE i
    choose t ht using fun k => Ideal.mem_span_singleton'.1 (hc k)
    refine ⟨t, ?_⟩
    have hcr := Matrix.mulVec_cramer (Matrix.transpose (Matrix.of v)) w
    have hcr_apply : ∀ k, Matrix.cramer (Matrix.transpose (Matrix.of v)) w k = (Matrix.of (Function.update v k w)).det := by
      intro k
      rw [Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
      rfl
    apply smul_right_injective (Fin n → 𝓞 L) hd0
    funext i
    have hi := congrFun hcr i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, hcr_apply,
      Matrix.det_transpose, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.mul_sum]
    calc (Matrix.of v).det * (u * w i) = u * ((Matrix.of v).det * w i) := by ring
      _ = u * ∑ k, v k i * (Matrix.of (Function.update v k w)).det := by rw [hi]
      _ = ∑ k, (Matrix.of v).det * (t k * v k i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        linear_combination (-(v k i)) * ht k

theorem exists_coord_lattice {M : Type} [AddCommGroup M] [Module (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (F : Submodule (𝓞 L) M) {n : ℕ} (x : Fin n → M) (hx : ∀ i, x i ∈ F) (hli : LinearIndependent (𝓞 L) x)
    (c : 𝓞 L) (hc : c ≠ 0) (hF : ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x)) :
    ∃ E : Submodule (𝓞 L) (Fin n → 𝓞 L), (∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k) ∧ detIdeal E ≠ ⊥ ∧
      Ideal.absNorm (Ideal.span {c ^ n}) =
        (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup * Ideal.absNorm (detIdeal E) := by
  set Φ : (Fin n → 𝓞 L) →ₗ[𝓞 L] M := Fintype.linearCombination (𝓞 L) x with hΦ
  have hΦa : ∀ w, Φ w = ∑ k, w k • x k := fun w => Fintype.linearCombination_apply _ _ _
  have hΦi : Function.Injective Φ := by
    intro a b h
    have h' := Fintype.linearIndependent_iff.1 hli (a - b) (by
      rw [← hΦa, map_sub, h, sub_self])
    funext i
    exact sub_eq_zero.1 (h' i)
  have hrange : Submodule.span (𝓞 L) (Set.range x) = LinearMap.range Φ := by
    rw [hΦ, Fintype.range_linearCombination]
  set ψ : M →ₗ[𝓞 L] M := c • LinearMap.id with hψ
  have hψa : ∀ z, ψ z = c • z := fun z => rfl
  have hψi : Function.Injective ψ := by
    intro a b h
    rw [hψa, hψa] at h
    exact smul_right_injective M hc h
  set E : Submodule (𝓞 L) (Fin n → 𝓞 L) := (F.map ψ).comap Φ with hE
  have hmem : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k := by
    intro w
    simp only [hE, Submodule.mem_comap, Submodule.mem_map, hψa, hΦa]
  set A : Submodule (𝓞 L) (Fin n → 𝓞 L) :=
    LinearMap.range (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L))).mulVecLin with hA
  have hAmem : ∀ w, w ∈ A ↔ ∃ v, c • v = w := by
    intro w
    simp [hA, Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAE : A ≤ E := by
    intro w hw
    obtain ⟨v, rfl⟩ := (hAmem w).1 hw
    rw [hmem]
    refine ⟨Φ v, ?_, ?_⟩
    · rw [hΦa]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)
    · rw [hΦa, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
  have hdet : detIdeal E ≠ ⊥ := by
    intro hb
    have h1 := det_mem_detIdeal E (fun i => c • Pi.single i (1 : 𝓞 L)) (fun i => hAE ((hAmem _).2 ⟨_, rfl⟩))
    rw [hb, Ideal.mem_bot] at h1
    have e1 : Matrix.of (fun i => c • Pi.single i (1 : 𝓞 L)) = c • (1 : Matrix (Fin n) (Fin n) (𝓞 L)) := by
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e1, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact pow_ne_zero n hc h1
  refine ⟨E, hmem, hdet, ?_⟩
  have iA : A.toAddSubgroup.index = Ideal.absNorm (Ideal.span {c ^ n}) := by
    rw [Ideal.absNorm_span_singleton]
    have := card_quotient_mulVecLin (K := L) (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L)))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; exact pow_ne_zero n hc)
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  have iE : E.toAddSubgroup.index = Ideal.absNorm (detIdeal E) := card_quotient_eq_absNorm_detIdeal n E
  have m1 : A.toAddSubgroup.map Φ.toAddMonoidHom =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.map ψ.toAddMonoidHom := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, rfl⟩ := (hAmem w).1 hw
      exact ⟨Φ v, by rw [hrange]; exact ⟨v, rfl⟩, by rw [hψa, map_smul]⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hrange] at hy
      obtain ⟨v, rfl⟩ := hy
      exact ⟨c • v, (hAmem _).2 ⟨v, rfl⟩, by rw [hψa, map_smul]⟩
  have m2 : E.toAddSubgroup.map Φ.toAddMonoidHom = F.toAddSubgroup.map ψ.toAddMonoidHom := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hw)
      exact ⟨y, hy, he⟩
    · rintro ⟨y, hy, rfl⟩
      have h2 := hF y hy
      rw [hrange] at h2
      obtain ⟨w, hw⟩ := h2
      refine ⟨w, ?_, by rw [hw, hψa]⟩
      exact Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨y, hy, by rw [hw, hψa]⟩)
  have hrel : A.toAddSubgroup.relIndex E.toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := Φ.toAddMonoidHom) _ _ hΦi, m1, m2,
      AddSubgroup.relIndex_map_map_of_injective _ _ hψi]
  rw [← iA, ← AddSubgroup.relIndex_mul_index (show A.toAddSubgroup ≤ E.toAddSubgroup from hAE), hrel, iE]

theorem exists_local_frame {M : Type} [AddCommGroup M] [Module (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (F : Submodule (𝓞 L) M) {n : ℕ} (x : Fin n → M) (hx : ∀ i, x i ∈ F) (hli : LinearIndependent (𝓞 L) x)
    (c : 𝓞 L) (hc : c ≠ 0) (hF : ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x))
    (E : Submodule (𝓞 L) (Fin n → 𝓞 L)) (hE : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k) (hD : detIdeal E ≠ ⊥)
    (p : Nat.Primes) (j : L →+* ℂ_[p]) :
    ∃ (y : Fin n → M) (s : 𝓞 L) (T : Matrix (Fin n) (Fin n) (𝓞 L)), (∀ k, y k ∈ F) ∧ LinearIndependent (𝓞 L) y ∧
      (∀ z ∈ F, ∃ u : 𝓞 L, ‖j (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) ∧ ‖j (s : L)‖ = 1 ∧
      (∀ i, s • x i = ∑ k, T i k • y k) ∧ T.det ≠ 0 ∧
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) - logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E) =
        Real.log ‖j ((T.det : 𝓞 L) : L)‖ := by
  obtain ⟨v, u, hvE, hdet, hlog, hu, hspan⟩ := exists_max_det E hD p j
  have hz : ∀ i, ∃ z ∈ F, c • z = ∑ k, v i k • x k := fun i => (hE (v i)).1 (hvE i)
  choose y hyF hy using hz
  have hinj : Function.Injective (fun z : M => c • z) := smul_right_injective M hc
  have key : ∀ z ∈ F, ∃ t : Fin n → 𝓞 L, u • z = ∑ k, t k • y k := by
    intro z hz
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 (hF z hz)
    have hwE : w ∈ E := (hE w).2 ⟨z, hz, hw.symm⟩
    obtain ⟨t, ht⟩ := hspan w hwE
    refine ⟨t, hinj ?_⟩
    have e1 : c • (u • z) = ∑ l, (u • w) l • x l := by
      rw [smul_comm, ← hw, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    have e2 : ∑ l, (u • w) l • x l = ∑ k, t k • (c • y k) := by
      rw [ht]
      simp only [hy, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_smul]
      exact Finset.sum_comm
    show c • (u • z) = c • ∑ k, t k • y k
    rw [e1, e2, Finset.smul_sum]
    simp only [smul_comm (t _) c]
  choose T0 hT using fun i => key (x i) (hx i)
  set T : Matrix (Fin n) (Fin n) (𝓞 L) := Matrix.of T0 with hTdef
  have hTV : T * Matrix.of v = (u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L)) := by
    refine Matrix.ext fun i l => ?_
    have h0 := (Fintype.linearIndependent_iff.1 hli)
      (fun l => (T * Matrix.of v) i l - ((u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L))) i l) ?_ l
    · exact sub_eq_zero.1 h0
    · simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.sum_smul, smul_smul]
      rw [sub_eq_zero, Finset.sum_comm]
      calc ∑ k, ∑ l, (T i k * v k l) • x l = ∑ k, T0 i k • (c • y k) := by
            simp only [hy, Finset.smul_sum, smul_smul, hTdef, Matrix.of_apply]
        _ = c • (u • x i) := by
            rw [hT i, Finset.smul_sum]
            simp only [smul_comm c]
        _ = (u * c) • x i := by rw [smul_smul, mul_comm]
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hdetT : T.det * (Matrix.of v).det = (u * c) ^ n := by
    rw [← Matrix.det_mul, hTV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hTne : T.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetT
    exact pow_ne_zero n (mul_ne_zero hu0 hc) hdetT.symm
  have hji : Function.Injective (j.comp (algebraMap (𝓞 L) L)) :=
    j.injective.comp (IsFractionRing.injective (𝓞 L) L)
  have hc' : logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) = Real.log ‖j ((c : L))‖ * n := by
    rw [(GlobalTheory.T.log_ideal_mul_span_map L p _ hji).2.1]
    simp [map_pow, norm_pow, Real.log_pow, mul_comm]
  have hnorm : ‖j (T.det : L)‖ * ‖j ((Matrix.of v).det : L)‖ = ‖j (c : L)‖ ^ n := by
    have := congrArg (fun a : 𝓞 L => ‖j (a : L)‖) hdetT
    simpa [map_pow, map_mul, norm_pow, norm_mul, hu] using this
  have hpos1 : ‖j (T.det : L)‖ ≠ 0 := by
    simpa using hTne
  have hpos2 : ‖j ((Matrix.of v).det : L)‖ ≠ 0 := by
    simpa using hdet
  refine ⟨y, u, T, hyF, ?_, fun z hz => ?_, hu, fun i => by simpa [hTdef] using hT i, hTne, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : Matrix.vecMul g (Matrix.of v) = 0 := by
      rw [Fintype.linearIndependent_iff] at hli
      funext l
      refine hli (Matrix.vecMul g (Matrix.of v)) ?_ l
      have := congrArg (fun z => c • z) hg
      simp only [Finset.smul_sum, smul_comm c (g _), hy, smul_zero, Finset.smul_sum, smul_smul] at this
      rw [Finset.sum_comm] at this
      simpa [Matrix.vecMul, dotProduct, Finset.sum_smul] using this
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet h1)
  · obtain ⟨t, ht⟩ := key z hz
    refine ⟨u, hu, ?_⟩
    rw [ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [hc', hlog]
    have := congrArg Real.log hnorm
    rw [Real.log_mul hpos1 hpos2, Real.log_pow] at this
    linarith

end Local

private theorem exists_logNorms_lemma {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {n : ℕ} (x : Fin n → B.carrier) :
    Real.log (gramDet B.metric σ x) = Real.log ‖B.gramDet σ x‖ := by
  have heq : B.gramDet σ x = (Matrix.gram ℂ fun i => fibreVec B.metric σ (x i)).det := by
    unfold HermitianBundle.gramDet
    congr 1
  have hnn := (Matrix.posSemidef_gram ℂ (fun i => fibreVec B.metric σ (x i))).det_nonneg
  obtain ⟨r, hr, hz⟩ := RCLike.nonneg_iff_exists_ofReal.1 hnn
  unfold gramDet
  rw [heq, ← hz]
  simp [RCLike.norm_ofReal, abs_of_nonneg hr]

private theorem exists_logNorms_lemma_2 {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (x : Fin n → B.carrier) (hx : ∀ i, x i ∈ F)
    (hli : LinearIndependent (𝓞 L) x) (hn : B.rank F = n) :
    ∃ c : 𝓞 L, c ≠ 0 ∧ ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x) := by
  let s : Fin n → F := fun i => ⟨x i, hx i⟩
  have hsli : LinearIndependent (𝓞 L) s := LinearIndependent.of_comp F.subtype hli
  let S := Submodule.span (𝓞 L) (Set.range s)
  have hF : Module.rank (𝓞 L) F = n := by
    rw [← hn, HermitianBundle.rank]
    exact (Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm
  have hS : Module.rank (𝓞 L) S = n := by
    rw [rank_span hsli, Cardinal.mk_range_eq s hsli.injective, Cardinal.mk_fin]
  have hQ := rank_quotient_add_rank_of_isDomain S
  rw [hS, hF] at hQ
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 (𝓞 L) (F ⧸ S))
  rw [hk] at hQ
  have hk0 : k = 0 := by
    have : ((k + n : ℕ) : Cardinal) = (n : Cardinal) := by rw [Nat.cast_add]; exact hQ
    have := Nat.cast_injective this
    omega
  have hr : Module.rank (𝓞 L) (F ⧸ S) = 0 := by rw [hk, hk0, Nat.cast_zero]
  have htor := rank_eq_zero_iff.1 hr
  choose a ha0 hav using htor
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 L) (M := F ⧸ S)
  refine ⟨∏ i, a (g i), Finset.prod_ne_zero_iff.2 fun i _ => ha0 _, fun z hz => ?_⟩
  have key : ∀ q : F ⧸ S, (∏ i, a (g i)) • q = 0 := by
    intro q
    have hq : q ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun i => a (g i)) (Finset.mem_univ i)
      rw [hd, mul_comm, mul_smul, hav, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul r y _ hy => rw [smul_comm, hy, smul_zero]
  have h1 := key (Submodule.Quotient.mk ⟨z, hz⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  have h2 := Submodule.mem_map_of_mem (f := F.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

theorem exists_logNorms {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (x : Fin n → B.carrier) (hx : ∀ i, x i ∈ F)
    (hli : LinearIndependent (𝓞 L) x) (hn : B.rank F = n) :
    ∃ N : Fl.LogNorms L, N.IsAdelic ∧ N.deg = B.normDegree F ∧ (∀ σ, N.inf σ = Real.log ‖B.gramDet σ x‖ / 2) ∧
      ∀ (p : Nat.Primes) (j : L →+* ℂ_[p]), ∃ (y : Fin n → B.carrier) (s : 𝓞 L) (T : Matrix (Fin n) (Fin n) (𝓞 L)),
        (∀ k, y k ∈ F) ∧ LinearIndependent (𝓞 L) y ∧
        (∀ z ∈ F, ∃ u : 𝓞 L, ‖j (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) ∧ ‖j (s : L)‖ = 1 ∧
        (∀ i, s • x i = ∑ k, T i k • y k) ∧ T.det ≠ 0 ∧ N.fin p j = Real.log ‖j ((T.det : 𝓞 L) : L)‖ := by
  obtain ⟨c, hc, hF⟩ := exists_logNorms_lemma_2 B F x hx hli hn
  obtain ⟨E, hE, hD, hidx⟩ := exists_coord_lattice F x hx hli c hc hF
  have hcn : Ideal.span {c ^ n} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hc
  let N : Fl.LogNorms L := ⟨fun σ => Real.log ‖B.gramDet σ x‖ / 2,
    fun p j => logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) -
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)⟩
  set idx := (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup with hidx_def
  have hprod : Ideal.absNorm (Ideal.span {c ^ n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hcn
  rw [hidx] at hprod
  have hi0 : idx ≠ 0 := left_ne_zero_of_mul hprod
  have hd0 : Ideal.absNorm (detIdeal E) ≠ 0 := right_ne_zero_of_mul hprod
  have hfs : N.finSum = fun p : Nat.Primes => Real.log ‖((idx : ℚ) : ℂ_[p])‖ := by
    funext p
    have e1 := GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hcn p
    have e2 := GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hD p
    have hne1 : ‖((idx : ℕ) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hi0)
    have hne2 : ‖((Ideal.absNorm (detIdeal E) : ℕ) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hd0)
    show ∑ j : L →+* ℂ_[p], (logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) -
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)) = _
    rw [Finset.sum_sub_distrib, e1, e2, hidx, Nat.cast_mul, norm_mul, Real.log_mul hne1 hne2, Rat.cast_natCast]
    ring
  have hpf := (GlobalTheory.T.rat_product_formula (idx : ℚ) (Nat.cast_ne_zero.2 hi0)).2
  let s : Fin n → F := fun i => ⟨x i, hx i⟩
  have hsli : LinearIndependent (𝓞 L) s := LinearIndependent.of_comp F.subtype hli
  have hsub : (Submodule.span (𝓞 L) (Set.range s)).toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.addSubgroupOf F.toAddSubgroup := by
    ext ⟨z, hz⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    simp only [Submodule.mem_toAddSubgroup,
      Submodule.mem_span_range_iff_exists_fun, Subtype.ext_iff, Submodule.coe_sum, Submodule.coe_smul, s]
  have hcard : Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range s)) = idx := by
    rw [hidx_def, AddSubgroup.relIndex, AddSubgroup.index, ← hsub]
    rfl
  have hdeg := HermitianBundle.degree_eq_of_linearIndependent B F hsli (by rw [Fintype.card_fin, hn])
  refine ⟨N, ?_, ?_, fun σ => rfl, fun p j => ?_⟩
  · refine ((GlobalTheory.T.logIdeal_support_finite L _ hcn).union (GlobalTheory.T.logIdeal_support_finite L _ hD)).subset ?_
    rintro p ⟨j, hj⟩
    by_contra hc'
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hc'
    exact hj (by show _ - _ = (0 : ℝ); rw [hc'.1, hc'.2, sub_zero])
  · unfold Fl.LogNorms.deg HermitianBundle.normDegree
    rw [hfs, hdeg, hcard]
    simp only [exists_logNorms_lemma]
    have hq : ‖((idx : ℚ) : ℂ)‖ = (idx : ℝ) := by simp
    rw [hq] at hpf
    have hsum : ∑ σ : L →+* ℂ, N.inf σ = (∑ σ : L →+* ℂ, Real.log ‖B.gramDet σ x‖) / 2 := by
      rw [Finset.sum_div]
    rw [hsum]
    congr 1
    linarith
  · obtain ⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩ := exists_local_frame F x hx hli c hc hF E hE hD p j
    exact ⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩

theorem finite_finSum {k : Type} [Field k] [NumberField k] {N : Fl.LogNorms k} (h : N.IsAdelic) :
    (Function.support N.finSum).Finite := by
  refine h.subset fun p hp => ?_
  by_contra h0
  simp only [Set.mem_setOf_eq, not_exists, not_not] at h0
  exact hp (Finset.sum_eq_zero fun j _ => h0 j)

theorem deg_eq_sub {k L L' : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Field L'] [NumberField L']
    (β : k →+* L') (e : L →+* L') (N : Fl.LogNorms k) (N₁ N₂ : Fl.LogNorms L) (a : L') (ha : a ≠ 0)
    (hN : N.IsAdelic) (h₁ : N₁.IsAdelic) (h₂ : N₂.IsAdelic)
    (hinf : ∀ s : L' →+* ℂ, N.inf (s.comp β) = Real.log ‖s a‖ + N₁.inf (s.comp e) - N₂.inf (s.comp e))
    (hfin : ∀ (p : Nat.Primes) (j : L' →+* ℂ_[p]),
      N.fin p (j.comp β) = Real.log ‖j a‖ + N₁.fin p (j.comp e) - N₂.fin p (j.comp e)) :
    N.deg = N₁.deg - N₂.deg := by
  obtain ⟨hd, _⟩ := GlobalTheory.T.logNorms_ext_degree_adelic k L' β N
  obtain ⟨hd₁, ha₁⟩ := GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₁
  obtain ⟨hd₂, ha₂⟩ := GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₂
  obtain ⟨_, hpf⟩ := GlobalTheory.T.product_formula_log_norms L' a ha
  have f0 := finite_finSum (GlobalTheory.T.log_norms_of_nonzero_adelic L' a ha)
  have f1 := finite_finSum (ha₁.2 h₁)
  have f2 := finite_finSum (ha₂.2 h₂)
  rw [← hd, ← hd₁, ← hd₂]
  have hs : (LogNorms.ext β N).finSum = fun p => (LogNorms.ofElt a).finSum p +
      (LogNorms.ext e N₁).finSum p - (LogNorms.ext e N₂).finSum p := by
    funext p
    simp only [LogNorms.finSum, LogNorms.ext, LogNorms.ofElt, hfin, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  have hfs : ∑ᶠ p, (LogNorms.ext β N).finSum p = ∑ᶠ p, (LogNorms.ofElt a).finSum p +
      ∑ᶠ p, (LogNorms.ext e N₁).finSum p - ∑ᶠ p, (LogNorms.ext e N₂).finSum p := by
    rw [hs, finsum_sub_distrib ((f0.union f1).subset (Function.support_add _ _)) f2,
      finsum_add_distrib f0 f1]
  have hi : ∑ s, (LogNorms.ext β N).inf s = ∑ s : L' →+* ℂ, Real.log ‖s a‖ +
      ∑ s, (LogNorms.ext e N₁).inf s - ∑ s, (LogNorms.ext e N₂).inf s := by
    simp only [LogNorms.ext, hinf, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold LogNorms.deg
  rw [hi, hfs, ← sub_div]
  congr 1
  linarith [hpf]

end LevelTowerAlt
end
end

section
open NumberField GlobalTheory.CompanionTheory.Ar

namespace LevelTowerAlt

theorem logOm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (_ : NeZero H.d) (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ ∧ |(GlobalTheory.CM.logOm E χ).re| ≤ C * (1 + Real.log (hostRd E) + |hostLval H|) := by
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  refine ⟨1 + Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|, by positivity, ?_⟩
  intro E _ _ _ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  refine ⟨⟨H.d_prime.ne_zero⟩, (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ),
    GlobalTheory.isKroneckerChar_quadraticChar (by have := H.d_mod; omega), ?_⟩
  have hL : (GlobalTheory.CM.logOm E ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - hostLval H := by
    simp only [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]
    rfl
  have hrd : rootDiscr E = hostRd E := by
    unfold hostRd rootDiscr
    rw [Int.cast_abs, one_div]
  have h1 : 1 ≤ hostRd E := by
    unfold hostRd
    apply Real.one_le_rpow
    · have := Int.one_le_abs (NumberField.discr_ne_zero E)
      rw [← Int.cast_abs]
      exact_mod_cast this
    · positivity
  have hb0 : 0 ≤ Real.log (hostRd E) := Real.log_nonneg h1
  have hlogdiv : Real.log (2 * Real.pi / rootDiscr E) = Real.log (2 * Real.pi) - Real.log (hostRd E) := by
    rw [hrd, Real.log_div (by positivity) (by linarith)]
  rw [hL, hlogdiv]
  have ha1 := le_abs_self (Real.log (2 * Real.pi))
  have ha2 := neg_abs_le (Real.log (2 * Real.pi))
  have hl1 := le_abs_self (hostLval H)
  have hl2 := neg_abs_le (hostLval H)
  have hb : |Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log (hostRd E)) - hostLval H| ≤
      Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)| + Real.log (hostRd E) + |hostLval H| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hm : 0 ≤ (Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|) *
      (Real.log (hostRd E) + |hostLval H|) := by positivity
  nlinarith

end LevelTowerAlt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open TensorProduct

namespace LevelTowerAlt

theorem mem_eigSp {R W O : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing O] (ρ : O →+* Module.End R W)
    (σ : O →+* R) (x : W) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigSp_baseChange {E : Type} [Field E] [NumberField E] {O R M W : Type} [CommRing O] [CommRing R] [Algebra O R]
    [Module.Flat O R] [AddCommGroup M] [Module O M] [AddCommGroup W] [Module R W] [Module O W] [IsScalarTower O R W]
    (j : M →ₗ[O] W) (hj : IsBaseChange R j) (ρM : 𝓞 E →+* Module.End O M) (ρW : 𝓞 E →+* Module.End R W)
    (h : ∀ a z, ρW a (j z) = j (ρM a z)) (s : 𝓞 E →+* O) :
    eigSp ρW ((algebraMap O R).comp s) = Submodule.span R (j '' (eigSp ρM s : Set M)) := by
  classical
  refine le_antisymm (fun w hw => ?_) (Submodule.span_le.2 ?_)
  · let b := RingOfIntegers.basis E
    let Φ := fun i => ρM (b i) - s (b i) • (LinearMap.id : M →ₗ[O] M)
    have hker : LinearMap.ker (LinearMap.pi Φ) ≤ eigSp ρM s := by
      intro z hz
      have h1 : ∀ i, ρM (b i) z = s (b i) • z := fun i => sub_eq_zero.1 (congrFun hz i)
      rw [mem_eigSp]
      intro a
      rw [← b.sum_repr a]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_smul, smul_assoc]
    obtain ⟨u, rfl⟩ := hj.equiv.surjective w
    have h2 : ∀ i (u : R ⊗[O] M), hj.equiv ((Φ i).lTensor R u) =
        ρW (b i) (hj.equiv u) - algebraMap O R (s (b i)) • hj.equiv u := by
      intro i u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r z =>
        rw [LinearMap.lTensor_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, h, smul_comm, ← smul_sub, algebraMap_smul,
          ← j.map_smul, ← j.map_sub]
        rfl
      | add x y hx hy =>
        rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
        abel
    have h3 : ∀ i, (Φ i).lTensor R u = 0 := fun i => by
      apply hj.equiv.injective
      rw [h2, map_zero, (mem_eigSp _ _ _).1 hw]
      exact sub_self _
    have h4 : LinearMap.pi Φ = ∑ i, LinearMap.single O (fun _ => M) i ∘ₗ Φ i := by
      ext z i
      simp [Finset.sum_apply, Pi.single_apply]
    have h5 : (LinearMap.pi Φ).lTensor R u = 0 := by
      rw [h4, ← LinearMap.coe_lTensorHom, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.coe_lTensorHom, LinearMap.lTensor_comp, LinearMap.comp_apply, h3, map_zero]
    obtain ⟨u', rfl⟩ := (Module.Flat.lTensor_exact R (LinearMap.exact_subtype_ker_map (LinearMap.pi Φ)) u).1 h5
    clear hw h3 h5
    induction u' using TensorProduct.induction_on with
    | zero => simp
    | tmul r z =>
      rw [LinearMap.lTensor_tmul, hj.equiv_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hker z.2, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
  · rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_eigSp] at hz ⊢
    intro a
    rw [h, hz, map_smul, RingHom.comp_apply, algebraMap_smul]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem spDual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← spMap_comp]
  congr 1
  exact RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem spDual_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem left_eq_of_cart {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {x : Sp A ⟶ S'} {x' : Sp B ⟶ S'} (hx : x' = spMap g ≫ x)
    (v : epsAt x ⟶ t'.G) (v' : epsAt x' ⟶ t'.G) (h : v'.left ≫ m.φ = spMap (dualMap g) ≫ v.left ≫ m.φ) :
    v'.left = spMap (dualMap g) ≫ v.left := by
  refine m.cart.1.hom_ext (h.trans (Category.assoc _ _ _).symm) ?_
  have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap B (DualNumber B)) ≫ x' := Over.w v'
  have h2 : v.left ≫ t'.G.hom = spMap (algebraMap A (DualNumber A)) ≫ x := Over.w v
  rw [h1, Category.assoc, h2, ← Category.assoc, spDual_alg, hx, Category.assoc]

theorem push_model {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {R : Type} [CommRing R] {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) {W : Type} [AddCommGroup W] [Module R W]
    (M' : LieModel t'.G x' W) (ρ : 𝓞 E →+* Module.End R W) (hρ : M'.IsActOf t'.act.act ρ) :
    ∃ M : LieModel t.G x W, M.IsActOf t.act.act ρ ∧ ∀ u, (M'.pt u).left ≫ m.φ = (M.pt u).left := by
  subst hx
  obtain ⟨M, hM⟩ := (GlobalTheory.T.lie_model_pullback_equivalence S S' t.G t'.G f m.φ m.cart R x' W).2 M'
  refine ⟨M, fun a e => Over.OverMorphism.ext ?_, hM⟩
  rw [← hM, hρ a e, Over.comp_left, Over.comp_left, ← hM, Category.assoc, Category.assoc, m.act a]

variable {L : Type} [Field L] [NumberField L] {t' : SAB H (Sp (𝓞 L))} {M : Type} [AddCommGroup M] [Module (𝓞 L) M]
  (MB : LieModel t'.G (𝟙 _) M) {ρM : 𝓞 E →+* Module.End (𝓞 L) M}

theorem exists_model (hρ : MB.IsActOf t'.act.act ρM) {S : Scheme.{0}} {t : SAB H S} {f : S ⟶ Sp (𝓞 L)}
    (m : SABMap t t' f) {R : Type} [CommRing R] [IsDomain R] (g : 𝓞 L →+* R) (hg : Function.Injective g)
    (x : Sp R ⟶ S) (hx : x ≫ f = spMap g) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (MW : LieModel t.G x W) (ρW : 𝓞 E →+* Module.End R W)
      (j : M →+ W), MW.IsActOf t.act.act ρW ∧
      (∀ z, (MW.pt (j z)).left ≫ m.φ = spMap (dualMap g) ≫ (MB.pt z).left) ∧ (∀ a z, j (a • z) = g a • j z) ∧
      ∀ (s : 𝓞 E →+* 𝓞 L) (n : ℕ) (y : Fin n → M), (∀ k, y k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) y →
        (∀ z ∈ eigSp ρM s, ∃ u, IsUnit (g u) ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) →
        LinearIndependent R (fun k => j (y k)) ∧
          Submodule.span R (Set.range fun k => j (y k)) = eigSp ρW (g.comp s) := by
  letI : Algebra (𝓞 L) R := g.toAlgebra
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨W, _, _, ⟨M₁⟩⟩ := lieModel_exists _ t'.G R (spMap g ≫ 𝟙 _)
  letI : Module (𝓞 L) W := Module.compHom W g
  haveI : IsScalarTower (𝓞 L) R W := ⟨fun a b e => by
    show (g a * b) • e = g a • b • e
    rw [mul_smul]⟩
  obtain ⟨j₀, hj₀, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear _ t'.G (𝓞 L) R g (𝟙 _) M W MB M₁
  let j : M →ₗ[𝓞 L] W := { toFun := j₀, map_add' := map_add j₀, map_smul' := fun a e => j₀.map_smulₛₗ a e }
  have hbc : IsBaseChange R j := GlobalTheory.T.lie_model_isBaseChange _ t'.G (𝓞 L) R (𝟙 _) M W MB M₁ j hj₀
  have key : ∀ (x₀ : Sp R ⟶ Sp (𝓞 L)) (M₀ : LieModel t'.G x₀ W), x₀ = x ≫ f →
      ∃ M' : LieModel t.G x W, ∀ e, (M'.pt e).left ≫ m.φ = (M₀.pt e).left := by
    rintro _ M₀ rfl
    exact (GlobalTheory.T.lie_model_pullback_equivalence _ S t'.G t.G f m.φ m.cart R x W).1 M₀
  obtain ⟨MW, hMW⟩ := key _ M₁ (by rw [hx, Category.comp_id])
  have hl : ∀ z, (MW.pt (j z)).left ≫ m.φ = spMap (dualMap g) ≫ (MB.pt z).left := fun z =>
    (hMW _).trans ((Category.comp_id _).symm.trans (hj₀ z))
  obtain ⟨ρW, hρW, -⟩ := lieModel_exists_unique_act S t.G R x W MW _ t.act.act t.act.hom t.act.one t.act.mul t.act.add
  have heq : ∀ a z, ρW a (j z) = j (ρM a z) := by
    intro a z
    refine MW.inj ?_
    rw [hρW a (j z)]
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)
    · have h1 : (MB.pt (ρM a z)).left = (MB.pt z).left ≫ (t'.act.act a).left := by
        rw [hρ a z]
        rfl
      change ((MW.pt (j z)).left ≫ (t.act.act a).left) ≫ m.φ = (MW.pt (j (ρM a z))).left ≫ m.φ
      rw [Category.assoc, m.act a, ← Category.assoc, hl z, hl (ρM a z), h1, Category.assoc]
    · rw [Over.w, Over.w]
  haveI : Module.IsTorsionFree (𝓞 L) R := .of_smul_eq_zero fun a r h =>
    (mul_eq_zero.1 h).imp_left fun h0 => hg (h0.trans (map_zero g).symm)
  refine ⟨W, inferInstance, inferInstance, MW, ρW, j.toAddMonoidHom, hρW, hl, fun a z => j.map_smul a z,
    fun s n y hy hli hsp => ⟨?_, ?_⟩⟩
  · have h1 := (Module.Flat.linearIndependent_one_tmul (S := R) hli).map' hbc.equiv.toLinearMap hbc.equiv.ker
    have h2 : (hbc.equiv.toLinearMap ∘ fun k => (1 : R) ⊗ₜ[𝓞 L] y k) = fun k => j (y k) := by
      funext k
      exact (hbc.equiv_tmul 1 (y k)).trans (one_smul _ _)
    rwa [h2] at h1
  · refine Eq.trans ?_ (eigSp_baseChange j hbc ρM ρW heq s).symm
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      exact ⟨y k, hy k, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨u, hu, h1⟩ := hsp z hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 h1
      have h2 : g u • j z = ∑ k, g (c k) • j (y k) := by
        refine (j.map_smul u z).symm.trans ?_
        rw [← hc, map_sum]
        exact Finset.sum_congr rfl fun k _ => j.map_smul _ _
      refine (Submodule.smul_mem_iff_of_isUnit _ hu).1 ?_
      rw [h2]
      exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem finrank_of_lieMult {S : Scheme.{0}} {t : SAB H S} {k : Type} [Field k] {x : Sp k ⟶ S} {W : Type}
    [AddCommGroup W] [Module k W] (MW : LieModel t.G x W) {ρW : 𝓞 E →+* Module.End k W}
    (hρ : MW.IsActOf t.act.act ρW) {τ : 𝓞 E →+* k} {n : ℕ} (h : LieMult t.act x τ n) :
    Module.finrank k (eigSp ρW τ) = n := by
  obtain ⟨v, hv⟩ := h
  have hv' : IsEigFrame t.act x τ v := hv
  choose u hu using fun i => MW.onto (v i) (hv'.1 i).1
  have e : v = fun i => MW.pt (u i) := funext fun i => (hu i).symm
  rw [e] at hv'
  obtain ⟨h1, h2⟩ := (((GlobalTheory.T.lie_model_eigenvectors_action S k t.G x W MW).2 _ t.act ρW τ hρ).2 n u).1 hv'
  rw [← h2, finrank_span_eq_card h1, Fintype.card_fin]

end LevelTowerAlt
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace LevelTowerAlt.Gram

theorem exists_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), (∀ i, IsTanAt t.G x (v i)) → ∃ Γ : Matrix (Fin n) (Fin n) ℂ, IsHodgeGram t.G t.PP.L x v Γ := by
  intro E _ _ _ H S t hp hA hK x n v hv
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H S t hp hA hK ℂ x
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, -, hAH, -, d₁, -⟩ := GlobalTheory.thetaUnifAV_all Q rig hrig
  have hl : ∀ a, ∃ t' : epsR ℂ ⟶ Q.A, t'.left ≫ ψ = (v a).left ∧ IsTangent t' := by
    intro a
    have sq : (v a).left ≫ t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := Over.w (v a)
    let t' : epsR ℂ ⟶ Q.A := Over.homMk (hQ.1.lift _ _ sq) (hQ.1.lift_snd _ _ _)
    have h1 : t'.left ≫ ψ = (v a).left := hQ.1.lift_fst _ _ _
    refine ⟨t', h1, (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hQ t').2 ?_⟩
    rw [h1]
    exact hv a
  choose t' h1 h2 using hl
  choose W hW _ using fun a => d₁ (t' a) (h2 a)
  exact ⟨Matrix.of fun a b => Real.pi * hermForm Hm (W a) (W b), Q, ψ, t', u, Hm, χ, W, hQ, hQL.symm, hAH,
    fun a => ⟨h1 a, hW a⟩, fun _ _ => rfl⟩

theorem gram_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (Γ Γ' : Matrix (Fin n) (Fin n) ℂ), L.IsLB → (∀ i, IsTanAt G x (v i)) → IsHodgeGram G L x v Γ → (∀ p q, HodgeIP G L x (v p) (v q) (Γ' p q)) → Γ' = Γ.transpose := by
  intro S G _ L x n v Γ Γ' hL hv hG hIP
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := hG
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  obtain ⟨ht₁, ht₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all Q u
  have htan : ∀ a, IsTangent (v' a) := fun a =>
    (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hp (v' a)).2 (by rw [(hvW a).1]; exact hv a)
  ext p q
  obtain ⟨-, -, -, A, _, φ, g, u', Hm', χ', a', b', a, b, h1, h2, h3, h4, h5, h6, e⟩ :=
    hodgeInnerProduct_iff_hodgeForm.1 (hIP p q)
  have key := GlobalTheory.T.hol_unif_compare_isogeny S G L x Q.A A ψ φ Q.g g (GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u) u' Hm Hm' χ χ'
    hL Q.isAb hp h1 ht₁ ht₂ (GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH) h2 (v' q) (v' p) a' b' (W q) (W p) a b
    (htan q) (htan p) (h3.trans (hvW q).1.symm) (h4.trans (hvW p).1.symm) (hvW q).2 (hvW p).2 h5 h6
  rw [e, key, Matrix.transpose_apply, hΓ]

end LevelTowerAlt.Gram
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights TensorProduct

set_option linter.unusedSectionVars false

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {R : Type} [CommRing R] {x' : Sp R ⟶ S'} {x : Sp R ⟶ S} (hx : x = x' ≫ f) (v' : epsAt x' ⟶ t'.G) :
    ∃ v : epsAt x ⟶ t.G, v'.left ≫ m.φ = v.left := by
  refine ⟨Over.homMk (v'.left ≫ m.φ) ?_, rfl⟩
  have h1 : v'.left ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x' := Over.w v'
  change (v'.left ≫ m.φ) ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, h1, hx, Category.assoc]

theorem hodgeInnerProduct_pushforward_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {x' : Sp ℂ ⟶ S'} {x : Sp ℂ ⟶ S} (hx : x = x' ≫ f) {v' w' : epsAt x' ⟶ t'.G} {v w : epsAt x ⟶ t.G}
    (hv : v'.left ≫ m.φ = v.left) (hw : w'.left ≫ m.φ = w.left) (c : ℂ) :
    HodgeIP t'.G t'.PP.L x' v' w' c ↔ HodgeIP t.G t.PP.L x v w c := by
  subst hx
  exact (GlobalTheory.T.hodge_inner_product_pullback_unique E H S' S t' t f m x' v' w' v w hv hw).1 c

theorem exists_smul_mem_span {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (hn : B.rank F = n) :
    ∃ x : Fin n → B.carrier, (∀ i, x i ∈ F) ∧ LinearIndependent (𝓞 L) x ∧
      ∀ z ∈ F, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x) := by
  subst hn
  obtain ⟨y, hy⟩ := B.exists_linearIndependent_rank F
  have hfin := finite_quotient_span hy (Fintype.card_fin _)
  refine ⟨fun i => (y i : B.carrier), fun i => (y i).2, hy.map' F.subtype F.ker_subtype, fun z hz => ?_⟩
  refine ⟨(Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range y)) : 𝓞 L), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
  have h1 := card_nsmul_eq_zero' (G := F ⧸ Submodule.span (𝓞 L) (Set.range y)) (x := Submodule.Quotient.mk ⟨z, hz⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  have h2 := Submodule.mem_map_of_mem (f := F.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  rw [Nat.cast_smul_eq_nsmul]
  exact h2

variable {L : Type} [Field L] [NumberField L] {t' : SAB H (Sp (𝓞 L))} {B : HermitianBundle.{0} L}
  (MB : LieModel t'.G (𝟙 _) B.carrier) {ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier}

theorem rank_eig (hρ : MB.IsActOf t'.act.act ρM) {tB : SAB H (Sp L)} (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    (σ : L →+* ℂ) (s : 𝓞 E →+* 𝓞 L) {n : ℕ}
    (h : LieMult tB.act (spMap σ) ((σ.comp (algebraMap (𝓞 L) L)).comp s) n) : B.rank (eigSp ρM s) = n := by
  have hg : Function.Injective (σ.comp (algebraMap (𝓞 L) L)) := σ.injective.comp (IsFractionRing.injective _ _)
  obtain ⟨W, _, _, MW, ρW, j, h1, -, -, h2⟩ := exists_model MB hρ m' _ hg (spMap σ) (spMap_comp _ _).symm
  obtain ⟨x, hx, hli, hsp⟩ := exists_smul_mem_span B (eigSp ρM s) rfl
  obtain ⟨h3, h4⟩ := h2 s _ x hx hli fun z hz => (hsp z hz).imp fun u hu =>
    ⟨IsUnit.mk0 _ ((map_ne_zero_iff _ hg).2 hu.1), hu.2⟩
  rw [← finrank_of_lieMult MW h1 h, ← h4, finrank_span_eq_card h3, Fintype.card_fin]

theorem exists_vec (hρ : MB.IsActOf t'.act.act ρM) {S S₀ : Scheme.{0}} {tK : SAB H S} {f : S ⟶ Sp (𝓞 L)}
    (n : SABMap tK t' f) {t₀ : SAB H S₀} {f₀ : S ⟶ S₀} (mf : SABMap tK t₀ f₀) {K : Type} [Field K] (g : 𝓞 L →+* K)
    (hg : Function.Injective g) (x : Sp K ⟶ S) (hx : x ≫ f = spMap g) (x₀ : Sp K ⟶ S₀) (hx₀ : x₀ = x ≫ f₀) :
    ∃ (vK : B.carrier → (epsAt x ⟶ tK.G)) (vec : B.carrier → (epsAt x₀ ⟶ t₀.G)),
      (∀ z, (vK z).left ≫ n.φ = spMap (dualMap g) ≫ (MB.pt z).left) ∧ (∀ z, (vK z).left ≫ mf.φ = (vec z).left) ∧
      (∀ z, IsTanAt t₀.G x₀ (vec z)) ∧
      (∀ (s : 𝓞 E →+* 𝓞 L) (r : ℕ) (y : Fin r → B.carrier), (∀ k, y k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) y →
        (∀ z ∈ eigSp ρM s, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) →
        IsEigFrame t₀.act x₀ (g.comp s) fun k => vec (y k)) ∧
      ∀ (r : ℕ) (y : Fin r → B.carrier) (z : B.carrier) (u : 𝓞 L) (T : Fin r → 𝓞 L), u ≠ 0 →
        u • z = ∑ k, T k • y k → IsComb (fun k => (g u)⁻¹ * g (T k)) (fun k => vec (y k)) (vec z) := by
  obtain ⟨W, _, _, MW, ρW, j, h1, h2, h3, h4⟩ := exists_model MB hρ n g hg x hx
  obtain ⟨M₀, h5, h6⟩ := push_model mf hx₀ MW ρW h1
  have hb := GlobalTheory.T.lie_model_eigenvectors_action S₀ K t₀.G x₀ W M₀
  refine ⟨fun z => MW.pt (j z), fun z => M₀.pt (j z), h2, fun z => h6 _, fun z => M₀.tan _,
    fun s r y hy hli hsp => ?_, fun r y z u T hu h => ?_⟩
  · exact ((hb.2 _ t₀.act ρW _ h5).2 r fun k => j (y k)).2 (h4 s r y hy hli fun z hz => (hsp z hz).imp fun u hu =>
      ⟨IsUnit.mk0 _ ((map_ne_zero_iff _ hg).2 hu.1), hu.2⟩)
  · refine (hb.1 r _ (fun k => j (y k)) _).2 (congrArg M₀.pt ?_)
    have hu' : g u ≠ 0 := (map_ne_zero_iff _ hg).2 hu
    have h7 := congrArg j h
    rw [h3, map_sum] at h7
    simp only [h3] at h7
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h7, smul_smul, inv_mul_cancel₀ hu', one_smul]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {F : Type} [Field F] [NumberField F]
  {β : c.F →+* F} {e : L →+* F} {tK : SAB H (Sp F)} {y : Sp F ⟶ Xo.XF c} {U : Set (Xo.XF c)} {τ : E →+* ℂ}
  {φ : FrameFn Xo c} {s₁ s₂ : 𝓞 E →+* 𝓞 L}

theorem inf_norm (hρ : MB.IsActOf t'.act.act ρM) (hfib : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L)))) (mf : SABMap tK Xo.univ.t (under y))
    (hy : y ≫ pullback.snd _ _ = spMap β) (hU : Set.range y ⊆ U) (hφ : IsLineFn U τ φ)
    (hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁)
    (hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂)
    {vK : B.carrier → (epsAt (𝟙 (Sp F)) ⟶ tK.G)} {vec : B.carrier → (epsAt (under y) ⟶ Xo.univ.t.G)}
    (h1 : ∀ z, (vK z).left ≫ n.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt z).left)
    (h2 : ∀ z, (vK z).left ≫ mf.φ = (vec z).left) {x₁ : Fin D.p → B.carrier} {x₂ : Fin D.q → B.carrier}
    (hx₁ : (∀ i, x₁ i ∈ eigSp ρM s₁) ∧ LinearIndependent (𝓞 L) x₁ ∧
      ∀ z ∈ eigSp ρM s₁, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x₁))
    (hx₂ : (∀ i, x₂ i ∈ eigSp ρM s₂) ∧ LinearIndependent (𝓞 L) x₂ ∧
      ∀ z ∈ eigSp ρM s₂, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x₂))
    (hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k)) (s : F →+* ℂ) {r : ℝ}
    (hN : HasInfNorm U τ φ (s.comp β) r) :
    r = Real.log ‖s (φ F y (fun k => vec (x₁ k)) fun k => vec (x₂ k))‖ + Real.log ‖B.gramDet (s.comp e) x₁‖ / 2 -
      Real.log ‖B.gramDet (s.comp e) x₂‖ / 2 := by
  have hg : Function.Injective ((s.comp e).comp (algebraMap (𝓞 L) L)) :=
    (s.comp e).injective.comp (IsFractionRing.injective _ _)
  have hx : spMap s ≫ spMap (e.comp (algebraMap (𝓞 L) L)) = spMap ((s.comp e).comp (algebraMap (𝓞 L) L)) :=
    (spMap_comp _ _).symm
  obtain ⟨wK, wec, k1, k2, k3, k4, -⟩ := exists_vec MB hρ n mf _ hg (spMap s) hx (under (spMap s ≫ y))
    (Category.assoc _ _ _)
  have hfr' : IsFramed U τ (s.comp β) (spMap s ≫ y) (fun k => wec (x₁ k)) fun k => wec (x₂ k) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, hy, spMap_comp]
    · rintro _ ⟨a, rfl⟩
      exact hU ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rw [RingHom.comp_assoc, hs₁]
      exact k4 s₁ _ x₁ hx₁.1 hx₁.2.1 hx₁.2.2
    · rw [RingHom.comp_assoc, hs₂]
      exact k4 s₂ _ x₂ hx₂.1 hx₂.2.1 hx₂.2.2
  have hbc : ∀ z, (wec z).left = spMap (dualMap s) ≫ (vec z).left := fun z => by
    have h3 := left_eq_of_cart n s (Category.comp_id _).symm (vK z) (wK z) (by
      rw [k1, h1, ← Category.assoc, ← spDual_comp, RingHom.comp_assoc])
    rw [← k2, ← h2, h3, Category.assoc]
  have hnat := hφ.nat F ℂ s β y _ _ (spMap s ≫ y) (fun k => wec (x₁ k)) (fun k => wec (x₂ k)) hfr rfl
    (fun _ => hbc _) fun _ => hbc _
  have hgram : ∀ {m : ℕ} (x : Fin m → B.carrier), ∃ Γ, IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under (spMap s ≫ y))
      (fun k => wec (x k)) Γ ∧ Γ.det = B.gramDet (s.comp e) x := by
    intro m x
    obtain ⟨Γ, hΓ⟩ := Gram.exists_gram E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample Xo.univ.ktriv _ m
      (fun k => wec (x k)) fun k => k3 _
    refine ⟨Γ, hΓ, ?_⟩
    have hpt : spMap ((s.comp e).comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ =
        spMap s ≫ spMap (e.comp (algebraMap (𝓞 L) L)) := (Category.comp_id _).trans hx.symm
    choose vv hvv using fun z => exists_push n hpt (wK z)
    have hl : ∀ z, MB.Lifts ((s.comp e).comp (algebraMap (𝓞 L) L)) (𝟙 t'.G.left) z (vv z) := fun z =>
      (Category.comp_id _).trans ((hvv z).symm.trans (k1 z))
    have h3 := Gram.gram_eq _ Xo.univ.t.G Xo.univ.t.PP.L _ m (fun k => wec (x k)) Γ
      (Matrix.of fun i j => (B.metric.form (s.comp e)).inner ((1 : ComplexAt (s.comp e)) ⊗ₜ[𝓞 L] x i)
        ((1 : ComplexAt (s.comp e)) ⊗ₜ[𝓞 L] x j)) Xo.univ.t.PP.isLB (fun k => k3 _) hΓ fun i j =>
      (hodgeInnerProduct_pushforward_iff mf (Category.assoc _ _ _) (k2 _) (k2 _) _).1
        ((hodgeInnerProduct_pushforward_iff n hpt (hvv _) (hvv _) _).2 (hfib (s.comp e) (x i) (x j) _ _ (hl _) (hl _)))
    rw [HermitianBundle.gramDet, h3, Matrix.det_transpose]
  obtain ⟨Γ, hΓ, e1⟩ := hgram x₁
  obtain ⟨Δ, hΔ, e2⟩ := hgram x₂
  have h4 := hN _ _ _ Γ Δ hfr' hΓ hΔ
  rw [hnat, e1, e2] at h4
  rw [← h4]
  ring

theorem int_frame (hρ : MB.IsActOf t'.act.act ρM) (n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L))))
    (mf : SABMap tK Xo.univ.t (under y)) {V : Type} [CommRing V] [IsDomain V] [Algebra V F] (gV : 𝓞 L →+* V)
    (hgV : (algebraMap V F).comp gV = e.comp (algebraMap (𝓞 L) L)) {T : SAB H (Sp V)} (mT : SABMap T t' (spMap gV))
    (m'' : SABMap tK T (spMap (algebraMap V F))) (hm : n.φ = m''.φ ≫ mT.φ)
    {vK : B.carrier → (epsAt (𝟙 (Sp F)) ⟶ tK.G)} {vec : B.carrier → (epsAt (under y) ⟶ Xo.univ.t.G)}
    (h1 : ∀ z, (vK z).left ≫ n.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt z).left)
    (h2 : ∀ z, (vK z).left ≫ mf.φ = (vec z).left) (s : 𝓞 E →+* 𝓞 L) {r : ℕ} (x : Fin r → B.carrier)
    (hx : ∀ k, x k ∈ eigSp ρM s) (hli : LinearIndependent (𝓞 L) x)
    (hsp : ∀ z ∈ eigSp ρM s, ∃ u, IsUnit (gV u) ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x)) :
    IsIntFrame mf m'' ((e.comp (algebraMap (𝓞 L) L)).comp s) fun k => vec (x k) := by
  have hg : Function.Injective gV := by
    have h : Function.Injective ((algebraMap V F).comp gV) := by
      rw [hgV]
      exact e.injective.comp (IsFractionRing.injective _ _)
    exact Function.Injective.of_comp (f := algebraMap V F) h
  obtain ⟨W, _, _, MW, ρW, j, k1, k2, -, k4⟩ := exists_model MB hρ mT gV hg (𝟙 _) (Category.id_comp _)
  refine ⟨gV.comp s, fun k => MW.pt (j (x k)), ?_, ?_, fun k => ⟨(vK (x k)).left, h2 _, ?_⟩⟩
  · rw [← RingHom.comp_assoc, hgV]
  · exact (((GlobalTheory.T.lie_model_eigenvectors_action _ V T.G _ W MW).2 _ T.act ρW _ k1).2 r fun k => j (x k)).2 (k4 s r x hx hli hsp)
  · obtain ⟨v, hv⟩ := exists_push m'' (x := spMap (algebraMap V F) ≫ 𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (vK (x k))
    rw [hv]
    refine left_eq_of_cart mT (algebraMap V F) rfl _ v ?_
    rw [← hv, Category.assoc, ← hm, h1, k2, ← Category.assoc, ← spDual_comp, hgV]

theorem norm_det_eq {O F A : Type} [CommRing O] [Field F] [NormedField A] (g : O →+* F) (j : F →+* A) {r : ℕ} (u : O)
    (hu : ‖j (g u)‖ = 1) (T : Matrix (Fin r) (Fin r) O) :
    ‖j (Matrix.det (Matrix.of fun i k => (g u)⁻¹ * g (T i k)))‖ = ‖j (g T.det)‖ := by
  have h : (Matrix.of fun i k => (g u)⁻¹ * g (T i k)) = (g u)⁻¹ • g.mapMatrix T := by
    ext i k
    rfl
  rw [h, Matrix.det_smul, ← RingHom.map_det, map_mul, norm_mul, map_pow, norm_pow, map_inv₀, norm_inv, hu, inv_one,
    one_pow, _root_.one_mul]

theorem fin_norm (hρ : MB.IsActOf t'.act.act ρM)
    (n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L)))) (mf : SABMap tK Xo.univ.t (under y))
    (hy : y ≫ pullback.snd _ _ = spMap β) (hU : Set.range y ⊆ U) (hφ : IsLineFn U τ φ)
    (hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁)
    (hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂)
    {vK : B.carrier → (epsAt (𝟙 (Sp F)) ⟶ tK.G)} {vec : B.carrier → (epsAt (under y) ⟶ Xo.univ.t.G)}
    (h1 : ∀ z, (vK z).left ≫ n.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt z).left)
    (h2 : ∀ z, (vK z).left ≫ mf.φ = (vec z).left)
    (h3 : ∀ (s : 𝓞 E →+* 𝓞 L) (r : ℕ) (x : Fin r → B.carrier), (∀ k, x k ∈ eigSp ρM s) → LinearIndependent (𝓞 L) x →
      (∀ z ∈ eigSp ρM s, ∃ u : 𝓞 L, u ≠ 0 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range x)) →
      IsEigFrame Xo.univ.t.act (under y) ((e.comp (algebraMap (𝓞 L) L)).comp s) fun k => vec (x k))
    (h4 : ∀ (r : ℕ) (x : Fin r → B.carrier) (z : B.carrier) (u : 𝓞 L) (T : Fin r → 𝓞 L), u ≠ 0 →
      u • z = ∑ k, T k • x k → IsComb (fun k => (e.comp (algebraMap (𝓞 L) L) u)⁻¹ * e.comp (algebraMap (𝓞 L) L) (T k))
        (fun k => vec (x k)) (vec z))
    {x₁ y₁ : Fin D.p → B.carrier} {x₂ y₂ : Fin D.q → B.carrier}
    (hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k)) (p : Nat.Primes) (j : F →+* ℂ_[p])
    {u₁ u₂ : 𝓞 L} {T₁ : Matrix (Fin D.p) (Fin D.p) (𝓞 L)} {T₂ : Matrix (Fin D.q) (Fin D.q) (𝓞 L)}
    (a1 : ∀ k, y₁ k ∈ eigSp ρM s₁) (a2 : LinearIndependent (𝓞 L) y₁)
    (a3 : ∀ z ∈ eigSp ρM s₁, ∃ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y₁))
    (a4 : ‖j.comp e (u₁ : L)‖ = 1) (a5 : ∀ i, u₁ • x₁ i = ∑ k, T₁ i k • y₁ k) (a6 : T₁.det ≠ 0)
    (b1 : ∀ k, y₂ k ∈ eigSp ρM s₂) (b2 : LinearIndependent (𝓞 L) y₂)
    (b3 : ∀ z ∈ eigSp ρM s₂, ∃ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y₂))
    (b4 : ‖j.comp e (u₂ : L)‖ = 1) (b5 : ∀ i, u₂ • x₂ i = ∑ k, T₂ i k • y₂ k) (b6 : T₂.det ≠ 0) {r : ℝ}
    (hN : HasFinNorm U τ φ p (j.comp β) r) :
    r = Real.log ‖j (φ F y (fun k => vec (x₁ k)) fun k => vec (x₂ k))‖ + Real.log ‖j.comp e ((T₁.det : 𝓞 L) : L)‖ -
      Real.log ‖j.comp e ((T₂.det : 𝓞 L) : L)‖ := by
  obtain ⟨V, hV, hV1, hV2, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring F p j
  let gV : 𝓞 L →+* V := (e.comp (algebraMap (𝓞 L) L)).codRestrict V.toSubring fun a =>
    hV2 (RingOfIntegers.mapRingHom e a)
  have hgV : (algebraMap V F).comp gV = e.comp (algebraMap (𝓞 L) L) := rfl
  have hne : ∀ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 → u ≠ 0 := by
    rintro u hu rfl
    simp at hu
  have hunit : ∀ u : 𝓞 L, ‖j.comp e (u : L)‖ = 1 → IsUnit (gV u) := fun u hu => by
    have h0 : e (u : L) ≠ 0 := by
      intro h
      rw [RingHom.comp_apply, h] at hu
      simp at hu
    have h5 : (e (u : L))⁻¹ ∈ V := (hV1 _).1 (by
      rw [map_inv₀, norm_inv]
      exact (congrArg (·⁻¹) hu).trans_le inv_one.le)
    exact IsUnit.of_mul_eq_one ⟨_, h5⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  obtain ⟨T, ⟨mT⟩⟩ : ∃ T : SAB H (Sp V), Nonempty (SABMap T t' (spMap gV)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap gV) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m'', hm⟩ : ∃ m'' : SABMap tK _ (spMap (algebraMap V F)), n.φ = m''.φ ≫ mT.φ := by
    have key : ∀ (f : Sp F ⟶ Sp (𝓞 L)) (n : SABMap tK t' f), f = spMap (algebraMap V F) ≫ spMap gV →
        ∃ m'' : SABMap tK _ (spMap (algebraMap V F)), n.φ = m''.φ ≫ mT.φ := by
      rintro _ n rfl
      exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mT n
    exact key _ n (spMap_comp gV (algebraMap V F))
  have hfr' : IsFramed U τ β y (fun k => vec (y₁ k)) fun k => vec (y₂ k) :=
    ⟨hy, hU, hs₁ ▸ h3 s₁ _ y₁ a1 a2 fun z hz => (a3 z hz).imp fun u hu => ⟨hne u hu.1, hu.2⟩,
      hs₂ ▸ h3 s₂ _ y₂ b1 b2 fun z hz => (b3 z hz).imp fun u hu => ⟨hne u hu.1, hu.2⟩⟩
  have h5 := hN V F j β y _ _ _ tK mf m'' (fun a => (hV1 a).trans ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩) rfl
    hfr'
    (hs₁ ▸ int_frame MB hρ n mf gV hgV mT m'' hm h1 h2 s₁ y₁ a1 a2 fun z hz =>
      (a3 z hz).imp fun u hu => ⟨hunit u hu.1, hu.2⟩)
    (hs₂ ▸ int_frame MB hρ n mf gV hgV mT m'' hm h1 h2 s₂ y₂ b1 b2 fun z hz =>
      (b3 z hz).imp fun u hu => ⟨hunit u hu.1, hu.2⟩)
  have h6 := hφ.chg F β y _ _ _ _
    (Matrix.of fun i k => (e.comp (algebraMap (𝓞 L) L) u₁)⁻¹ * e.comp (algebraMap (𝓞 L) L) (T₁ i k))
    (Matrix.of fun i k => (e.comp (algebraMap (𝓞 L) L) u₂)⁻¹ * e.comp (algebraMap (𝓞 L) L) (T₂ i k)) hfr' hfr
    (fun i => h4 _ y₁ (x₁ i) u₁ (T₁ i) (hne _ a4) (a5 i)) fun i => h4 _ y₂ (x₂ i) u₂ (T₂ i) (hne _ b4) (b5 i)
  have h7 := congrArg (fun a => ‖j a‖) h6
  simp only [map_mul, norm_mul] at h7
  rw [norm_det_eq _ j u₁ a4, norm_det_eq _ j u₂ b4] at h7
  have hg : ∀ d : 𝓞 L, d ≠ 0 → ‖j (e.comp (algebraMap (𝓞 L) L) d)‖ ≠ 0 := fun d hd =>
    norm_ne_zero_iff.2 ((map_ne_zero j).2 ((map_ne_zero e).2
      ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hd)))
  have h8 := congrArg Real.log h7
  rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero j).2 (hφ.ne F β y _ _ hfr))) (hg _ a6),
    Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero j).2 (hφ.ne F β y _ _ hfr'))) (hg _ b6), h5] at h8
  exact eq_sub_of_add_eq h8.symm

end LevelTowerAlt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_im] using this
  have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_re] using this
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h2
      nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨by apply Complex.ext <;> simp [hre], fun h => ?_⟩
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

end LevelTowerAlt
end
