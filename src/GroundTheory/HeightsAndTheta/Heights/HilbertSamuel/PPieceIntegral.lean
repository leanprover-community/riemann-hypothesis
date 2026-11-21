import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenDegree
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem eval_eq_zero_of_block_zero {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f m) {x : (Σ k, ι k) → ℂ} {k : K}
    (hx : ∀ i, x ⟨k, i⟩ = 0) : eval x f = 0 := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw := hf (MvPolynomial.mem_support_iff.mp hd)
  obtain ⟨v, hv, hvk⟩ : ∃ v ∈ d.support, v.1 = k := by
    by_contra hno
    push Not at hno
    have h0 : (Finsupp.weight (blockWeight ι) d) k = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun v hv => ?_
      simp [blockWeight, hno v hv]
    have := hm k
    rw [hw] at h0
    omega
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
  obtain ⟨k', i⟩ := v
  subst hvk
  rw [hx i]
  exact zero_pow (Finsupp.mem_support_iff.mp hv)

variable [Fintype K] [∀ k, Fintype (ι k)]

theorem mem_radical_iff_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {m : K → ℕ} (hm : ∀ k, 1 ≤ m k)
    {f : MvPolynomial (Σ k, ι k) ℂ} (hf : IsWeightedHomogeneous (blockWeight ι) f m) :
    f ∈ I.radical ↔ f ∈ vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ) I]
  constructor
  · exact fun h => vanishingIdeal_anti_mono Set.inter_subset_left h
  · intro h x hx
    by_cases hU : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0
    · exact h x ⟨hx, hU⟩
    · push Not at hU
      obtain ⟨k, hk⟩ := hU
      exact eval_eq_zero_of_block_zero hm hf hk

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem finrank_gradedPiece_eq {P₁ P₂ : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (m : K → ℕ)
    (h : ∀ f ∈ weightedHomogeneousSubmodule ℂ (blockWeight ι) m, f ∈ P₁ ↔ f ∈ P₂) :
    Module.finrank ℂ (gradedPiece P₁ m) = Module.finrank ℂ (gradedPiece P₂ m) := by
  set W := weightedHomogeneousSubmodule ℂ (blockWeight ι) m
  let f₁ := (Ideal.Quotient.mkₐ ℂ P₁).toLinearMap ∘ₗ W.subtype
  let f₂ := (Ideal.Quotient.mkₐ ℂ P₂).toLinearMap ∘ₗ W.subtype
  have hr₁ : LinearMap.range f₁ = gradedPiece P₁ m := by
    simp only [f₁, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hr₂ : LinearMap.range f₂ = gradedPiece P₂ m := by
    simp only [f₂, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hk : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact h x hx
  rw [← hr₁, ← hr₂]
  exact ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hk)).trans
    f₂.quotKerEquivRange).finrank_eq

theorem hilbFn_radical_eq_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {m : K → ℤ} (hm : ∀ k, 1 ≤ m k) :
    hilbFn I.radical m = hilbFn (vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})) m := by
  unfold hilbFn
  have h0 : ∀ k, 0 ≤ m k := fun k => le_trans zero_le_one (hm k)
  rw [if_pos h0, if_pos h0]
  congr 1
  refine finrank_gradedPiece_eq _ fun f hf => mem_radical_iff_offBlocks I (m := fun k => (m k).toNat) (fun k => ?_) ?_
  · have := hm k
    omega
  · rwa [mem_weightedHomogeneousSubmodule] at hf

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (ι k)] in

theorem foldr_diffStep_eventuallyEq {h₁ h₂ : (K → ℤ) → ℤ} (h : h₁ =ᶠ[atTop] h₂) (l : List (K → ℤ)) :
    l.foldr diffStep h₁ =ᶠ[atTop] l.foldr diffStep h₂ := by
  induction l with
  | nil => exact h
  | cons b l ih =>
    have ht : Tendsto (fun m : K → ℤ => m - b) atTop atTop := by
      exact (tendsto_atTop_add_const_right atTop (-b) tendsto_id).congr fun m => by simp [sub_eq_add_neg]
    filter_upwards [ih, ht.eventually ih] with m hm hmb
    simp only [List.foldr_cons, diffStep, hm, hmb]

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (ι k)] in

theorem eventualValue_congr {f g : (K → ℤ) → ℤ} (h : f =ᶠ[atTop] g) : eventualValue f = eventualValue g := by
  unfold eventualValue
  have hiff : (∃ c, ∀ᶠ m in atTop, f m = c) ↔ ∃ c, ∀ᶠ m in atTop, g m = c :=
    ⟨fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.symm.trans hm.2⟩,
      fun ⟨c, hc⟩ => ⟨c, (h.and hc).mono fun _ hm => hm.1.trans hm.2⟩⟩
  by_cases hf : ∃ c, ∀ᶠ m in atTop, f m = c
  · rw [dif_pos hf, dif_pos (hiff.mp hf)]
    obtain ⟨m, hm⟩ := (hf.choose_spec.and ((hiff.mp hf).choose_spec.and h)).exists
    exact hm.1.symm.trans (hm.2.2.trans hm.2.1)
  · rw [dif_neg hf, dif_neg (mt hiff.mpr hf)]

theorem intNum_radical_eq_offBlocks (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum ℂ I.radical bs =
      intNum ℂ (vanishingIdeal ℂ (zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})) bs := by
  unfold intNum mixedDiff
  refine eventualValue_congr (foldr_diffStep_eventuallyEq ?_ _)
  filter_upwards [eventually_ge_atTop (1 : K → ℤ)] with m hm
  exact hilbFn_radical_eq_offBlocks I fun k => hm k

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem ptsIntegral_congr_integrand {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = g' z) : ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · have hd : ∀ y w, sheetDensity P hΨ.choose φ g y w = sheetDensity P hΨ.choose φ g' y w := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
      · rfl
    simp only [hd]
  · rfl

theorem PieceIntegral.proof (h : ClopenDegree.Statement) : PieceIntegral.Statement := by
  intro K _ _ ι _ P e L I hP hL hPI hopen
  set Z : Set ((Σ k, ι k) → ℂ) := {z | ∀ f ∈ I, eval z f = 0} with hZ
  set A := Z ∩ mcPts P with hA
  have h1 : ptsIntegral P (pot L) (Z.indicator fun _ => (1 : ℝ)) =
      ptsIntegral P (pot L) (A.indicator fun _ => (1 : ℝ)) := by
    refine ptsIntegral_congr_integrand P _ fun z hz => ?_
    by_cases hzZ : z ∈ Z
    · rw [Set.indicator_of_mem hzZ, Set.indicator_of_mem (show z ∈ A from ⟨hzZ, hz⟩)]
    · rw [Set.indicator_of_notMem hzZ, Set.indicator_of_notMem fun h' => hzZ h'.1]
  have hZc : IsClosed Z := by
    have hZi : Z = ⋂ f ∈ I, {z | eval z f = 0} := by
      ext z
      simp [hZ]
    rw [hZi]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
  have hcl : IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) := by
    constructor
    · have hpre : (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) = (↑) ⁻¹' Z := by
        ext ⟨z, hz⟩
        simp [hA]
      rw [hpre]
      exact hZc.preimage continuous_subtype_val
    · rw [isOpen_iff_mem_nhds]
      rintro ⟨z, hz⟩ ⟨hzZ, -⟩
      rw [nhds_subtype]
      exact ((hopen z hz hzZ).comap Subtype.val).mono fun y hy => ⟨hy y.2, y.2⟩
  have hAeq : A = zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp only [hA, hZ, mcPts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_zeroLocus_iff, aeval_eq_eval]
    constructor
    · rintro ⟨hz, hU, -⟩
      exact ⟨hz, hU⟩
    · rintro ⟨hz, hU⟩
      exact ⟨hz, hU, fun f hf => hz _ (hPI (Ideal.mem_map_of_mem _ hf))⟩
  rw [h1, h K ι P e L A hP hL Set.inter_subset_right hcl, intNum_radical_eq_offBlocks, hAeq]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
