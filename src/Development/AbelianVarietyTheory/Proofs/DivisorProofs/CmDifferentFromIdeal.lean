import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegOfLatRankEqZero
import BuildAid.ForwardExisting
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHom

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  first | exact @GlobalTheory.FlatCM.GramExists.exists_isGram | exact GlobalTheory.FlatCM.GramExists.exists_isGram | (intros; apply GlobalTheory.FlatCM.GramExists.exists_isGram <;> assumption)
end

section
section
open NumberField

namespace GlobalTheory

theorem ringOfIntegers_ringHom_injective {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : 𝓞 E →+* 𝓞 K) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem sum_log_norm_embeddings {K : Type} [Field K] [NumberField K] (y : K) :
    ∑ s : K →+* ℂ, Real.log ‖s y‖ = Real.log |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
  by_cases hy : y = 0
  · subst hy
    simp
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have h2 : ∏ s : K →+* ℂ, s y = ∏ s : K →ₐ[ℚ] ℂ, s y :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun s => rfl)
  rw [← Real.log_prod (fun s _ => by simpa using hy), ← norm_prod, h2, ← h]
  congr 1
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem mean_log_norm_embeddings_ringHom :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  intro E K _ _ _ _ σ x
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp σ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_ringHom_injective σ)
  let τ : E →+* K := IsFractionRing.lift hinj
  have hτ : τ (x : E) = (σ x : K) := IsFractionRing.lift_algebraMap hinj x
  letI : Algebra E K := τ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  have hx : (σ x : K) = algebraMap E K (x : E) := hτ.symm
  rw [sum_log_norm_embeddings, hx, ← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow,
    ← Module.finrank_mul_finrank ℚ E K]
  have h1 : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank E K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  rw [abs_pow, Real.log_pow]
  field_simp

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  atlas_forward_decl GlobalTheory.mean_log_norm_embeddings_ringHom
end

section
section
open NumberField

namespace GlobalTheory.SumIndex

theorem relIndex_pi_pi_of {ι G : Type} [Fintype ι] [AddCommGroup G] (A B : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ A).relIndex (AddSubgroup.pi Set.univ B) = ∏ i, (A i).relIndex (B i) := by
  let g : (∀ i, B i) →+ (AddSubgroup.pi Set.univ B) :=
    { toFun := fun v => ⟨fun i => (v i : G), fun i _ => (v i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hg : Function.Surjective g := fun x => ⟨fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ A).addSubgroupOf (AddSubgroup.pi Set.univ B)).comap g =
      AddSubgroup.pi Set.univ fun i => (A i).addSubgroupOf (B i) := by
    ext v
    simp [g, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hg, hc]
  simp_rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

theorem eq_zero_of_sum_eq_zero {ι R V : Type} [Fintype ι] [DecidableEq ι] [Ring R] [AddCommGroup V]
    [Module R V] (S : ι → Submodule R V) (hS : iSupIndep S) (y : ι → V) (hy : ∀ a, y a ∈ S a)
    (h0 : ∑ a, y a = 0) (b : ι) : y b = 0 := by
  have hb : y b = -∑ a ∈ Finset.univ.erase b, y a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hmem : y b ∈ ⨆ (a) (_ : a ≠ b), S a := by
    rw [hb]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a ha => ?_)
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase ha) (hy a))
  exact (Submodule.disjoint_def.1 (hS b)) _ (hy b) hmem

theorem relIndex_iSup_map_eq_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  intro K _ _ W V _ _ _ _ _ _ _ _ p M ℓ N hNℓ hinj hind
  classical
  let Φ : (Fin p → W) →ₗ[𝓞 K] V := ∑ a, ((M a).restrictScalars (𝓞 K)).comp (LinearMap.proj a)
  have hΦ : ∀ x, Φ x = ∑ a, M a (x a) := by intro x; simp [Φ]
  have himg : ∀ S : Submodule (𝓞 K) W, (Submodule.pi Set.univ (fun _ : Fin p => S)).map Φ =
      ⨆ a, S.map ((M a).restrictScalars (𝓞 K)) := by
    intro S
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hΦ]
      exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ⟨x a, hx a (Set.mem_univ a), rfl⟩
    · refine iSup_le fun a => ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨Pi.single a w, ?_, ?_⟩
      · intro b _
        by_cases h : b = a
        · subst h; simpa using hw
        · simp [Pi.single_apply, h]
      · rw [hΦ, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
        simp
  let Lp : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => ℓ)
  let Np : Submodule (𝓞 K) (Fin p → W) := Submodule.pi Set.univ (fun _ => N)
  have hNL : Np ≤ Lp := fun x hx a ha => hNℓ (hx a ha)
  let g : Lp.toAddSubgroup →+ V := Φ.toAddMonoidHom.comp Lp.toAddSubgroup.subtype
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun z hz => ?_
    have h0 : ∑ a, M a (z.1 a) = 0 := by rw [← hΦ]; exact hz
    have hy := eq_zero_of_sum_eq_zero _ hind (fun a => M a (z.1 a))
      (fun a => Submodule.subset_span ⟨z.1 a, z.2 a (Set.mem_univ a), rfl⟩) h0
    exact Subtype.ext (funext fun a => by simpa using hinj a (by simpa using hy a))
  have hL' : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup = (⊤ : AddSubgroup Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp [g, Lp]
  have hN' : (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      (Np.toAddSubgroup.addSubgroupOf Lp.toAddSubgroup).map g := by
    rw [← himg]
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
      AddSubgroup.mem_addSubgroupOf, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hNL hx, hx, rfl⟩
    · rintro ⟨x, _, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hL', hN', AddSubgroup.relIndex_map_map_of_injective _ _ hg, AddSubgroup.relIndex_top_right]
  change Np.toAddSubgroup.relIndex Lp.toAddSubgroup = _
  have e1 : Np.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => N.toAddSubgroup) := by
    ext x; simp [Np, AddSubgroup.mem_pi, Submodule.mem_pi]
  have e2 : Lp.toAddSubgroup = AddSubgroup.pi Set.univ (fun _ : Fin p => ℓ.toAddSubgroup) := by
    ext x; simp [Lp, AddSubgroup.mem_pi, Submodule.mem_pi]
  rw [e1, e2, relIndex_pi_pi_of, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.SumIndex
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : ℕ)
  (M : Fin p → (W →ₗ[K] V)) (ℓ N : Submodule (𝓞 K) W), N ≤ ℓ → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (⨆ a, N.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
    (N.toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
  atlas_forward_decl GlobalTheory.SumIndex.relIndex_iSup_map_eq_pow
end

section
section
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

open scoped ComplexOrder

theorem deg_iSup_map_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  intro K _ _ W V _ _ _ _ _ _ _ _ hW hV p M ℓ y hfg hrk hinj hind hgram
  have hr : Module.finrank K (Submodule.span K (ℓ : Set W)) = 1 := hrk
  haveI : FiniteDimensional K (Submodule.span K (ℓ : Set W)) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  obtain ⟨c, hcℓ, hc0⟩ : ∃ c ∈ ℓ, c ≠ 0 := by
    by_contra hne
    push_neg at hne
    have h0 : Submodule.span K (ℓ : Set W) = ⊥ := by
      rw [Submodule.span_eq_bot]; intro x hx; exact hne x hx
    rw [h0, finrank_bot] at hr; exact zero_ne_one hr
  have hspan : (ℓ : Set W) ⊆ Submodule.span K {c} := by
    have hle : Submodule.span K {c} ≤ Submodule.span K (ℓ : Set W) :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr hcℓ)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hr, finrank_span_singleton hc0])
    rw [heq]; exact Submodule.subset_span
  have hfℓ : IsFrame K ℓ ![c] := by
    refine ⟨fun i => by fin_cases i; simpa using hcℓ, ?_, ?_⟩
    · exact linearIndependent_unique_iff.mpr (by simpa using hc0)
    · intro x hx
      refine Submodule.span_mono ?_ (hspan hx)
      rintro _ rfl; exact ⟨0, rfl⟩
  set v : Fin p → V := fun a => M a c with hvdef
  have hvS : ∀ a, v a ∈ ℓ.map ((M a).restrictScalars (𝓞 K)) := fun a => ⟨c, hcℓ, rfl⟩
  have hfS : IsFrame K (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) v := by
    refine ⟨fun a => (le_iSup (fun a => ℓ.map ((M a).restrictScalars (𝓞 K))) a) (hvS a), ?_, ?_⟩
    · exact iSupIndep.linearIndependent _ hind (fun a => Submodule.subset_span (hvS a))
        (fun a h => hc0 (hinj a (h.trans (map_zero (M a)).symm)))
    · intro x hx
      have hle : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) ≤
          (Submodule.span K (Set.range v)).restrictScalars (𝓞 K) := by
        refine iSup_le fun a => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp (hspan hz)
        rw [Submodule.restrictScalars_mem, LinearMap.restrictScalars_apply, LinearMap.map_smul]
        exact Submodule.smul_mem _ k (Submodule.subset_span ⟨a, rfl⟩)
      exact hle hx
  have hSfg : (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).FG :=
    Submodule.fg_iSup _ (fun a => hfg.map _)
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex
      (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))).toAddSubgroup =
      ((Submodule.span (𝓞 K) {c}).toAddSubgroup.relIndex ℓ.toAddSubgroup) ^ p := by
    have h1 : Submodule.span (𝓞 K) (Set.range v) =
        ⨆ a, (Submodule.span (𝓞 K) {c}).map ((M a).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_range_eq_iSup]
      congr 1; funext a
      rw [Submodule.map_span, Set.image_singleton]; rfl
    rw [h1]
    exact GlobalTheory.T.relIndex_iSup_map_eq_relIndex_pow K W V p M ℓ _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hcℓ) hinj hind
  have hgr : ∀ s : K →+* ℂ, hV.gram s v = hW.form s c c • (s.mapMatrix y).transpose := by
    intro s; ext i j
    simp [HermFam.gram, v, hgram s j i c hcℓ, mul_comm]
  have hdet : ∀ s : K →+* ℂ, (hV.gram s v).det = (hW.form s c c) ^ p * s y.det := by
    intro s; rw [hgr, Matrix.det_smul, Matrix.det_transpose, RingHom.map_det, Fintype.card_fin]
  have hpos : ∀ s : K →+* ℂ, 0 < (hV.gram s v).det := fun s => (hV.posDef s p v hfS.2.1).det_pos
  have hA1 : ∀ s : K →+* ℂ, 0 < hW.form s c c := fun s => by
    have := (hW.posDef s 1 ![c] hfℓ.2.1).det_pos
    simpa [Matrix.det_fin_one] using this
  have hAeq : ∀ s : K →+* ℂ, hW.form s c c = (((hW.form s c c).re : ℝ) : ℂ) := fun s =>
    Complex.ext (by simp) (by simp [← (Complex.pos_iff.mp (hA1 s)).2])
  have hkey : ∀ s : K →+* ℂ, 0 < (s y.det).re ∧ (s y.det).im = 0 ∧
      (hV.gram s v).det.re = (hW.form s c c).re ^ p * (s y.det).re := by
    intro s
    have h1 := Complex.pos_iff.mp (hpos s)
    have hA := (Complex.pos_iff.mp (hA1 s)).1
    rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul] at h1
    have hApow : 0 < (hW.form s c c).re ^ p := pow_pos hA p
    refine ⟨pos_of_mul_pos_right h1.1 hApow.le, ?_, ?_⟩
    · exact (mul_eq_zero.mp h1.2.symm).resolve_left hApow.ne'
    · rw [hdet s, hAeq s, ← Complex.ofReal_pow, Complex.re_ofReal_mul]; simp
  have hlogV : ∀ s : K →+* ℂ, Real.log (hV.gram s v).det.re =
      p * Real.log (hW.form s c c).re + Real.log ‖s y.det‖ := by
    intro s
    obtain ⟨hre, him, heq⟩ := hkey s
    have hn : ‖s y.det‖ = (s y.det).re := by
      rw [← Complex.abs_re_eq_norm.mpr him, abs_of_pos hre]
    rw [heq, hn, Real.log_mul (pow_pos (Complex.pos_iff.mp (hA1 s)).1 p).ne' hre.ne', Real.log_pow]
  have hlogW : ∀ s : K →+* ℂ, Real.log (hW.gram s ![c]).det.re = Real.log (hW.form s c c).re := by
    intro s; simp [HermFam.gram, Matrix.det_fin_one]
  refine ⟨?_, ?_⟩
  · obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
    intro h; have := (hkey s).1; rw [h, map_zero] at this; simp at this
  · rw [arakelovDegree_eq_degreeOfFamily hV hSfg hfS, arakelovDegree_eq_degreeOfFamily hW hfg hfℓ]
    unfold degreeOfFamily
    have hrg : Set.range ![c] = {c} := by ext x; simp [eq_comm]
    rw [hrg, hidx, Nat.cast_pow, Real.log_pow, Finset.sum_congr rfl (fun s _ => hlogV s),
      Finset.sum_congr rfl (fun s _ => hlogW s), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

end GlobalTheory
end

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_iSup_map_rankOne_lattice_of_gram : ∀ (K : Type) [Field K] [NumberField K] (W V : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (hW : HermFam K W) (hV : HermFam K V) (p : ℕ) (M : Fin p → (W →ₗ[K] V)) (ℓ : Submodule (𝓞 K) W)
  (y : Matrix (Fin p) (Fin p) K), ℓ.FG → latRank K ℓ = 1 → (∀ a, Function.Injective (M a)) →
  iSupIndep (fun a => Submodule.span K ((ℓ.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) →
  (∀ (s : K →+* ℂ) a b, ∀ c ∈ ℓ, hV.form s (M b c) (M a c) = s (y a b) * hW.form s c c) →
  y.det ≠ 0 ∧ deg hV (⨆ a, ℓ.map ((M a).restrictScalars (𝓞 K))) =
    p * deg hW ℓ - (∑ s : K →+* ℂ, Real.log ‖s y.det‖) / (2 * Module.finrank ℚ K) := by
  atlas_forward_decl GlobalTheory.deg_iSup_map_of_gram
end

section
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section
namespace GlobalTheory.FlatCM.ImageDeg

open GlobalTheory.HermHom in

theorem form_diff_eq_pair : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
  (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K))
  (f₁ f₂ : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M₁ M₂ : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K))
  (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f₁ → IsMonHom f₂ →
  IsMonHom g → LamEq P'.L f₁ f₂ P.L g (𝟙 P.A) → F.IsDiffOf F' f₁ M₁ → F.IsDiffOf F' f₂ M₂ → F.IsDiffOf F g N →
  ∀ s c c', h'.form s (M₂ c) (M₁ c') = h.form s c (N c') := by
  intro hU hL K _ _ P F P' F' h h' f₁ f₂ g M₁ M₂ N hh hh' hf₁ hf₂ hg hlam hM₁ hM₂ hN s c c'
  obtain ⟨Q, φ, t, u, Hm, χ, W, hφ, hA, hW, hform⟩ := hh s
  obtain ⟨Q', φ', t', u', Hm', χ', W', hφ', hA', hW', hform'⟩ := hh' s
  obtain ⟨-, a₀, ha₀, ea₀, da⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₁ hf₁
  obtain ⟨-, b₀, hb₀, eb₀, db⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₂ hf₂
  obtain ⟨-, g₀, hg₀, eg₀, dg⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have hlam₀ : LamEq F'.P₀.L a₀ b₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    lamEq_baseChange _ _ (spMap (algebraMap (𝓞 K) K)) P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A
      F.φ F.φ F'.φ F.φ F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1
      P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB F.P₀.isLB F'.fib.2.2 F.fib.2.2 f₁ f₂ g (𝟙 _) a₀ b₀ g₀ (𝟙 _)
      ea₀ eb₀ eg₀ (by simp) hlam
  obtain ⟨a₁, ha₁, ea⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 a₀
  obtain ⟨b₁, hb₁, eb⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 b₀
  obtain ⟨g₁, hg₁, eg⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ.2.1 g₀
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨Φ₁, hΦ₁, -, hΦd₁, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' a₁ ha₁
  obtain ⟨Φ₂, hΦ₂, -, hΦd₂, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' b₁ hb₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have hlam₁ : LamEq Q'.L a₁ b₁ Q.L g₁ (𝟙 Q.A) :=
    lamEq_baseChange _ _ (spMap s) F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A φ φ φ' φ
      hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 a₀ b₀ g₀ (𝟙 _) a₁ b₁ g₁ (𝟙 _)
      ea eb eg (by simp) hlam₀
  have hweil := weilEq_of_lamEq hL ℂ Q Q Q' Q a₁ b₁ g₁ (𝟙 _) ha₁ hb₁ hg₁ inferInstance hlam₁
  have hherm := (weilEq_iff_hermForm_eq hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA a₁ b₁ g₁ (𝟙 _) Φ₁ Φ₂ G
    LinearMap.id hΦ₁ hΦ₂ hG (fun z => by simp)).1 hweil
  have e₁ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' ea hΦd₁ (da M₁ hM₁ c')
  have e₂ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' eb hΦd₂ (db M₂ hM₂ c)
  have e₃ := map_comb s hφ.2.1 hφ.2.1 u u F.basis.1 F.basis.1 hW hW t₁ eg hGd (dg N hN c')
  rw [form_eq h' s Hm' W' _ hform', form_eq h s Hm W _ hform, ← e₁, ← e₂, ← e₃, hherm, LinearMap.id_apply]

theorem gram_images : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
  [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol) (FB : GenFib B.pol)
  (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) (f₁ f₂ : A.t.G ⟶ B.t.G)
  (M₁ M₂ : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) (g : 𝓞 E), FA.IsHerm hA → FB.IsHerm hB →
  IsMonHom f₁ → IsMonHom f₂ →
  WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
  FA.IsDiffOf FB f₁ M₁ → FA.IsDiffOf FB f₂ M₂ → ∀ (τ : 𝓞 E →+* 𝓞 K) (s : K →+* ℂ),
  ∀ c ∈ FA.eigLat A.t.act τ, hB.form s (M₂ c) (M₁ c) = s (τ g : K) * hA.form s c c := by
  intro hU hL E _ _ _ H K _ _ σ₁ A B FA FB hA hB f₁ f₂ M₁ M₂ g hhA hhB hf₁ hf₂ hw hM₁ hM₂ τ s c hc
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K A.pol FA (𝓞 E) A.t.act
  have hg : IsMonHom (A.t.act.act g) := A.t.act.hom _
  have hinj : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hlam := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol f₁ f₂ (A.t.act.act g) (𝟙 _) hf₁ hf₂ hg inferInstance ℂ
    (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hinj hw
  have hf := form_diff_eq_pair hU hL K A.pol FA B.pol FB hA hB f₁ f₂ (A.t.act.act g) M₁ M₂ (r g) hhA hhB hf₁ hf₂ hg
    hlam hM₁ hM₂ (hr _) s c c
  have hev : r g c = (τ g : K) • c := ((he τ c).1.1 hc).2 _
  rw [hf]
  erw [hev]
  rw [HermFam.smul_right]

theorem side (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {K : Type} [Field K] [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol)
    (FB : GenFib B.pol) (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) {n : ℕ}
    (f : Fin n → (A.t.G ⟶ B.t.G)) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
    (g : Matrix (Fin n) (Fin n) (𝓞 E)) (τ : 𝓞 E →+* 𝓞 K) (Ω : ℝ) (hhA : FA.IsHerm hA) (hhB : FB.IsHerm hB)
    (hf : ∀ a, IsMonHom (f a))
    (hw : ∀ a b, WeilEq B.t.PP.L (f a) (f b) A.t.PP.L (A.t.act.act (g a b)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    (hM : ∀ a, FA.IsDiffOf FB (f a) (M a)) (hr : latRank K (FA.eigLat A.t.act τ) = 1)
    (hi : ∀ a, Function.Injective (M a))
    (hind : iSupIndep (fun a => Submodule.span K
      (((FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set (Fin FB.P₀.g → K))))
    (hΩ : 2 * deg hA (FA.eigLat A.t.act τ) = Ω) :
    g.det ≠ 0 ∧ deg hB (⨆ a, (FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K))) =
      n * (Ω / 2) - Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  set y : Matrix (Fin n) (Fin n) K := g.map fun x => (τ x : K) with hy
  have hgr : ∀ (s : K →+* ℂ) a b, ∀ c ∈ FA.eigLat A.t.act τ,
      hB.form s (M b c) (M a c) = s (y a b) * hA.form s c c := fun s a b c hc =>
    gram_images hU hL E H K σ₁ A B FA FB hA hB (f a) (f b) (M a) (M b) (g a b) hhA hhB (hf a) (hf b) (hw a b)
      (hM a) (hM b) τ s c hc
  obtain ⟨hne, hdeg⟩ := GlobalTheory.T.deg_iSup_map_rankOne_lattice_of_gram K _ _ hA hB n M _ y (GlobalTheory.CM.DegBound.eigLat_fg FA A.t.act τ) hr hi hind hgr
  have hdet : y.det = ((τ g.det : 𝓞 K) : K) := by
    rw [hy, show (fun x : 𝓞 E => (τ x : K)) = ⇑((algebraMap (𝓞 K) K).comp τ) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    rfl
  refine ⟨fun h0 => hne (by rw [hdet, h0, map_zero]; rfl), ?_⟩
  have hn := GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq E K τ g.det
  rw [hdeg, ← hΩ, hdet]
  have e : (∑ s : K →+* ℂ, Real.log ‖s ((τ g.det : 𝓞 K) : K)‖) / (2 * (Module.finrank ℚ K : ℝ)) =
      Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * (Module.finrank ℚ E : ℝ)) := by
    rw [mul_comm (2 : ℝ), ← div_div, hn, div_div, mul_comm]
  rw [e]
  ring

theorem deg_images : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  intro hC hU hL hE E _ _ _ H K _ _ ρ σ₁ p q X _ χ hχ gP gQ hG FP FQ FB MP MQ hDf h hh τ hτ
  have hD : DegSt := PureDeg.degSt hC hU hL hE
  obtain ⟨hP, hhP⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FP).1
  obtain ⟨hQ, hhQ⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FQ).1
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτ' : (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) H.rt = -ρ := by
    have e : (H.bar : 𝓞 E →+* 𝓞 E) H.rt = -H.rt := by simp
    rw [RingHom.comp_apply, e, map_neg, hτ]
  have hne : -ρ ≠ ρ := fun e => hρ (by
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero)
  let FA : ∀ b, GenFib (X.A b).pol := fun b => Bool.rec (motive := fun b => GenFib (X.A b).pol) FQ FP b
  let M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun j =>
    Sum.rec (motive := fun j => (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) MP MQ j
  have hM : ∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j) := by
    rintro (a | a)
    exacts [hDf.1 a, hDf.2 a]
  obtain ⟨-, -, hinj, hind, -⟩ := Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  have hrP := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ
  have hrQ := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) FQ 0 1 X.split X.typeM X.ρ_sq).1 (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))
  rw [if_pos hτ] at hrP
  rw [if_neg (by rw [hτ']; exact hne)] at hrQ
  have hΩP : 2 * deg hP (FP.eigLat (X.A true).t.act τ) = (logOm E χ).re := by
    have := hD E H χ hχ K ρ (X.A true) X.split X.ρ_sq X.typeP FP hP hhP τ hτ
    rw [← this, Complex.ofReal_re]
  have hΩQ := NumInh.deg_conjugate_type hD hχ X FQ hhQ hτ'
  have hindP := iSupIndep.comp (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin q), τ)) hind
    (fun a b e => Sum.inl_injective (congrArg Prod.fst e))
  have hindQ := iSupIndep.comp (f := fun a : Fin q => ((Sum.inr a : Fin p ⊕ Fin q), τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) hind
    (fun a b e => Sum.inr_injective (congrArg Prod.fst e))
  obtain ⟨h1, h2⟩ := side hU hL σ₁ (X.A true) X.B FP FB hP h (fun a => phiP X a) MP gP τ _ hhP hh
    (fun a => (X.lin (Sum.inl a)).1) hG.1 hDf.1 hrP (fun a => hinj (Sum.inl a)) hindP hΩP
  obtain ⟨h3, h4⟩ := side hU hL σ₁ (X.A false) X.B FQ FB hQ h (fun a => phiQ X a) MQ gQ
    (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) _ hhQ hh (fun a => (X.lin (Sum.inr a)).1) hG.2 hDf.2 hrQ
    (fun a => hinj (Sum.inr a)) hindQ hΩQ
  exact ⟨h1, h3, h2, h4⟩

end GlobalTheory.FlatCM.ImageDeg

end
end

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  atlas_forward_decl GlobalTheory.FlatCM.ImageDeg.deg_images
end

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  first | exact @GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | exact GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | (intros; apply GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx <;> assumption)
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_map_ringOfIntegers_hom' : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)), Module.finrank ℚ E ∣ Module.finrank ℚ K ∧ Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  first | exact @GlobalTheory.absNorm_map_ringOfIntegers_hom | exact GlobalTheory.absNorm_map_ringOfIntegers_hom | (intros; apply GlobalTheory.absNorm_map_ringOfIntegers_hom <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff

theorem latRank_iSup {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (N : ι → Submodule (𝓞 K) V)
    (hi : iSupIndep fun i => Submodule.span K (N i : Set V)) :
    latRank K (⨆ i, N i) = ∑ i, latRank K (N i) := by
  classical
  have hs : Submodule.span K ((⨆ i, N i : Submodule (𝓞 K) V) : Set V) = ⨆ i, Submodule.span K (N i : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun i => Submodule.span_mono ?_)
    · have : (⨆ i, N i) ≤ (⨆ i, Submodule.span K (N i : Set V)).restrictScalars (𝓞 K) :=
        iSup_le fun i => fun x hx => (le_iSup (fun i => Submodule.span K (N i : Set V)) i)
          (Submodule.subset_span hx)
      exact this
    · exact SetLike.coe_mono (le_iSup N i)
  unfold latRank
  rw [hs]
  have hinj : Function.Injective (DirectSum.coeLinearMap fun i => Submodule.span K (N i : Set V)) := by
    first
    | exact hi.dfinsupp_lsum_injective
    | exact (iSupIndep_iff_dfinsupp_lsum_injective _).1 hi
    | exact DirectSum.coeLinearMap_injective_of_iSupIndep hi
  rw [← DirectSum.range_coeLinearMap, LinearMap.finrank_range_of_inj hinj, Module.finrank_directSum]

end GlobalTheory.FlatCore.CMDiff

namespace GlobalTheory.FlatCore.CMDiff

theorem cmDiffSt_of_idealSt : IdealSt → GlobalTheory.FlatCore.CMDiffSt := by
  intro hI E _ _ _ H hH _ χ hχ K _ _ ρ σ₁ p q X F h hF τ hτ
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b =>
    (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A b).pol).some
  have hM : ∀ j : Fin p ⊕ Fin q, ∃ M, (FA j.isLeft).IsDiffOf F (X.φ j) M := fun j =>
    (DiffCoord.existsUnique_isDiffOf K _ (FA j.isLeft) _ F (X.φ j) (X.lin j).1).1.exists
  choose M hM using hM
  obtain ⟨gP, gQ, hg⟩ := GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject E H K ρ σ₁ p q X
  have hD : IsDiffs (FA true) (FA false) F (fun a => M (.inl a)) (fun a => M (.inr a)) :=
    ⟨fun a => hM (.inl a), fun a => hM (.inr a)⟩
  obtain ⟨𝔫, h𝔫, hid⟩ := hI E H hH K ρ σ₁ p q X gP gQ hg
  have hid' := hid (FA true) (FA false) F _ _ hD τ hτ
  obtain ⟨hP0, hQ0, hdP, hdQ⟩ :=
    GlobalTheory.T.degree_images_eigenLines_cmUnitaryShimuraObject GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H K ρ σ₁ p q X χ hχ gP gQ hg (FA true) (FA false) F _ _ hD h hF τ hτ
  obtain ⟨hle, hrk1, -, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p q X FA F M hM
  set τb : 𝓞 E →+* 𝓞 K := τ.comp (H.bar : 𝓞 E →+* 𝓞 E) with hτb
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτb' : τb H.rt = -ρ := by
    simp [hτb, GlobalTheory.CM.EigDec.bar_rt, hτ]
  have hne : ¬ τb H.rt = ρ := by
    rw [hτb']
    intro e
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact hρ ((mul_eq_zero.1 this).resolve_left two_ne_zero)
  have hdec := (GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ X.B F p q X.split X.typeB X.ρ_sq).1
  have hrkP : latRank K (F.eigLat X.B.t.act τ) = p := by rw [hdec, if_pos hτ]
  have hrkQ : latRank K (F.eigLat X.B.t.act τb) = q := by rw [hdec, if_neg hne]
  have hfg : ∀ σ, (F.eigLat X.B.t.act σ).FG := fun σ =>
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ F).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hsubP : subP (FA true) F (fun a => M (.inl a)) τ ≤ F.eigLat X.B.t.act τ :=
    iSup_le fun a => hle (.inl a, τ)
  have hsubQ : subQ (FA false) F (fun a => M (.inr a)) τb ≤ F.eigLat X.B.t.act τb :=
    iSup_le fun a => hle (.inr a, τb)
  have hrsP : latRank K (subP (FA true) F (fun a => M (.inl a)) τ) = p := by
    unfold subP
    beta_reduce
    refine (latRank_iSup (fun a : Fin p => ((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin q), τ))
      fun a b e => by simpa using e)).trans ?_
    have h1 : ∀ a : Fin p, latRank K (((FA true).eigLat (X.A true).t.act τ).map
        ((M (.inl a)).restrictScalars (𝓞 K))) = 1 := fun a => by
      have := hrk1 (.inl a, τ)
      simpa [hτ] using this
    calc _ = ∑ _a : Fin p, 1 := Finset.sum_congr rfl fun a _ => h1 a
      _ = p := by simp
  have hrsQ : latRank K (subQ (FA false) F (fun a => M (.inr a)) τb) = q := by
    unfold subQ
    beta_reduce
    refine (latRank_iSup (fun a : Fin q => ((FA false).eigLat (X.A false).t.act τb).map
        ((M (.inr a)).restrictScalars (𝓞 K)))
      (iSupIndep.comp hind (f := fun a : Fin q => ((Sum.inr a : Fin p ⊕ Fin q), τb))
      fun a b e => by simpa using e)).trans ?_
    have h1 : ∀ a : Fin q, latRank K (((FA false).eigLat (X.A false).t.act τb).map
        ((M (.inr a)).restrictScalars (𝓞 K))) = 1 := fun a => by
      have := hrk1 (.inr a, τb)
      simpa [hτb'] using this
    calc _ = ∑ _a : Fin q, 1 := Finset.sum_congr rfl fun a _ => h1 a
      _ = q := by simp
  obtain ⟨hneP, hdegP⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h p _ _ hsubP (hfg τ) hrkP hrsP
  obtain ⟨hneQ, hdegQ⟩ := GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index K _ h q _ _ hsubQ (hfg τb) hrkQ hrsQ
  rw [hdegP, hdegQ, hdP, hdQ]

  have hdvd := (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ ⊥).1
  have hfE : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfK : 0 < Module.finrank ℚ K := Module.finrank_pos
  set n := Module.finrank ℚ K / Module.finrank ℚ E with hn
  have hnK : (Module.finrank ℚ K : ℝ) = n * Module.finrank ℚ E := by
    rw [hn, Nat.cast_div hdvd (by exact_mod_cast hfE.ne')]
    field_simp
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hfK hdvd) hfE
  have hbar : Ideal.absNorm (𝔫.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔫 := by
    rw [(GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E E _ 𝔫).2, Nat.div_self hfE, pow_one]
  have hnorm : ∀ x : 𝓞 E, (Ideal.absNorm (Ideal.span {x}) : ℝ) = |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| := fun x => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast
    rfl
  have hspan : Ideal.span {τ gQ.det} = (Ideal.span {gQ.det}).map τ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at hid'
  have e1 := congrArg Ideal.absNorm hid'
  rw [map_mul, map_mul, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2, (GlobalTheory.T.absNorm_map_ringOfIntegers_hom' E K τ _).2] at e1
  have e2 := congrArg Ideal.absNorm h𝔫
  rw [map_mul, hbar, ← Ideal.span_singleton_mul_span_singleton, map_mul] at e2

  have hA : (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneP)
  have hB : (Ideal.absNorm (idx K q (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hneQ)
  have hP1 : (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hP0))
  have hQ1 : (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 (Ideal.span_singleton_eq_bot.not.2 hQ0))
  have hN1 : (Ideal.absNorm 𝔫 : ℝ) ≠ 0 := by
    intro h0
    have : ((Ideal.absNorm 𝔫 * Ideal.absNorm 𝔫 : ℕ) : ℝ) = 0 := by push_cast; rw [h0, zero_mul]
    rw [e2] at this
    push_cast at this
    exact (mul_ne_zero hP1 hQ1) this
  have l1 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e1
  have l2 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e2
  simp only [Nat.cast_mul, Nat.cast_pow] at l1 l2
  rw [Real.log_mul hA (pow_ne_zero _ hQ1), Real.log_mul (pow_ne_zero _ hN1) hB, Real.log_pow, Real.log_pow] at l1
  rw [Real.log_mul hN1 hN1, Real.log_mul hP1 hQ1] at l2
  rw [← hnorm, ← hnorm]
  have hfE' : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast hfE.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have key : Real.log (Ideal.absNorm (idx K p (F.eigLat X.B.t.act τ) (subP (FA true) F (fun a => M (.inl a)) τ)) : ℝ)
        / Module.finrank ℚ K
      - Real.log (Ideal.absNorm (idx K q (F.eigLat X.B.t.act τb) (subQ (FA false) F (fun a => M (.inr a)) τb)) : ℝ)
        / Module.finrank ℚ K =
      Real.log (Ideal.absNorm (Ideal.span {gP.det}) : ℝ) / (2 * Module.finrank ℚ E)
        - Real.log (Ideal.absNorm (Ideal.span {gQ.det}) : ℝ) / (2 * Module.finrank ℚ E) := by
    rw [← sub_div, ← sub_div, hnK]
    rw [div_eq_div_iff (mul_ne_zero hn' hfE') (mul_ne_zero two_ne_zero hfE')]
    linear_combination (2 * Module.finrank ℚ E : ℝ) * l1 + (n : ℝ) * (Module.finrank ℚ E : ℝ) * l2
  linear_combination key

end GlobalTheory.FlatCore.CMDiff

end
end
