import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdSt

section
noncomputable section

namespace PI.VolStabW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))

def am (i : ι) : ℝ≥0 := (m i (L i)).toNNReal

def tl (S : Finset ι) : ℝ≥0 := ∏' i : {i // i ∉ S}, am m L i.1

def TailH : Prop :=
  ∀ S : Finset ι, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c

variable {m L}

lemma hasProd_tl (hT : TailH m L) (S : Finset ι) :
    HasProd (fun i : {i // i ∉ S} => am m L i.1) (tl m L S) := by
  obtain ⟨c, hc, h⟩ := hT S
  have h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal := by
    have h3 := (ENNReal.tendsto_toNNReal hc).comp h
    refine h3.congr ?_
    intro s
    simp [Function.comp_def, am, ENNReal.toNNReal_prod]
  unfold tl
  rw [h2.tprod_eq]
  exact h2

lemma hasProd_ind (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := by
  have h := hasProd_tl hT S
  exact hasProd_subtype_iff_mulIndicator.mp h

lemma tl_split [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by
  classical
  have h1 := hasProd_ind hT S
  have h2 := hasProd_ind hT T
  have h3 : HasProd (((T \ S : Finset ι) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have h5 : HasProd (((T \ S : Finset ι) : Set ι).mulIndicator (am m L))
        (∏ b ∈ T \ S, ((T \ S : Finset ι) : Set ι).mulIndicator (am m L) b) := hasProd_prod_of_ne_finset_one (fun b hb => Set.mulIndicator_apply_eq_one.mpr (fun hb' => absurd (Finset.mem_coe.mp hb') hb))
    convert h5 using 1
    exact Finset.prod_congr rfl (fun i hi => (Set.mulIndicator_of_mem (Finset.mem_coe.mpr hi) _).symm)
  have h4 := h3.mul h2
  refine h1.unique ?_
  convert h4 using 1
  funext i
  by_cases hiS : i ∈ S
  · have hiT := h hiS
    simp [Set.mulIndicator_apply, hiT, hiS]
  · by_cases hiT : i ∈ T <;> simp [Set.mulIndicator_apply, hiT, hiS]

lemma tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by
  rw [tl_split hT (Finset.subset_insert i S), Finset.prod_eq_zero (i := i) (by simp [hi]) h0, zero_mul]

variable (m L)

def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)

lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by
  constructor
  rw [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.1 h.2

open Classical in

def Qm (S : Finset ι) : Measure (∀ i : {i // i ∉ S}, W i) :=
  if h : ∀ i, i ∉ S → m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤ then
    haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (h i.1 i.2)
    tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)
  else 0

instance Qm_fin (S : Finset ι) : IsFiniteMeasure (Qm m L S) := by
  unfold Qm; split_ifs with h
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    infer_instance
  · infer_instance

def Rm (S : Finset ι) : Measure (∀ i : {i // i ∈ S}, W i) :=
  Measure.pi (fun i : {i // i ∈ S} => (m i.1).restrict (L i.1)ᶜ)

open Classical in

def eS (S : Finset ι) : (∀ i, W i) ≃ᵐ (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i) :=
  MeasurableEquiv.piEquivPiSubtypeProd W (fun i => i ∈ S)

def kap [∀ i, SigmaFinite (m i)] (S : Finset ι) : Measure (∀ i, W i) :=
  ((Rm m L S).prod (Qm m L S)).map (eS S).symm

open Classical in

def mu (S : Finset ι) (i : ι) : Measure (W i) :=
  if i ∈ S then (m i).restrict (L i)ᶜ else (m i).restrict (L i)

open Classical in
lemma eS_symm_apply (S : Finset ι) (p : (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i))
    (i : ι) : (eS S).symm p i = if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := by
  simp only [eS, MeasurableEquiv.piEquivPiSubtypeProd]
  rfl

variable [∀ i, SigmaFinite (m i)]

instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance

variable {m L}

lemma kap_eval_null {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by
  classical
  have hs : MeasurableSet {x : ∀ j, W j | x i ∈ A} := measurable_pi_apply i hA
  unfold kap
  rw [Measure.map_apply (eS S).symm.measurable hs]
  by_cases hi : i ∈ S
  · have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = ((fun f => f ⟨i, hi⟩) ⁻¹' A) ×ˢ (Set.univ : Set (∀ j : {j // j ∉ S}, W j)) := by
      ext p
      simp [eS_symm_apply, hi]
    have hR : Rm m L S ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
      unfold Rm
      apply Measure.pi_eval_preimage_null
      simpa [mu, hi] using h
    rw [hpre, Measure.prod_prod, hR, zero_mul]
  · have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = (Set.univ : Set (∀ j : {j // j ∈ S}, W j)) ×ˢ ((fun f => f ⟨i, hi⟩) ⁻¹' A) := by
      ext p
      simp [eS_symm_apply, hi]
    have h' : (m i).restrict (L i) A = 0 := by simpa [mu, hi] using h
    have hQ : Qm m L S ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hh
      · haveI : ∀ j : {j // j ∉ S}, IsProbabilityMeasure (Pn m L j.1) := fun j => Pn_prob m L (hh j.1 j.2)
        have h6 : Measure.infinitePi (fun j : {j // j ∉ S} => Pn m L j.1) ((fun f => f ⟨i, hi⟩) ⁻¹' A) = 0 := by
          rw [← Measure.map_apply (measurable_pi_apply (⟨i, hi⟩ : {j // j ∉ S})) hA, Measure.infinitePi_map_eval]
          simp [Pn, h']
        simp [Measure.smul_apply, h6]
      · simp
    rw [hpre, Measure.prod_prod, hQ, mul_zero]

lemma kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by
  classical
  rw [ae_all_iff]
  intro i
  by_cases hi : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hi, Measure.restrict_apply (hLm i)])
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hxi
    exact hx ⟨fun _ => hxi, fun h => absurd hi h⟩
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hi, Measure.restrict_apply (hLm i).compl])
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
    by_contra hxi
    exact hx ⟨fun h => absurd h hi, fun _ => hxi⟩

end PI.VolStabW.RPA
end
end

section
noncomputable section

namespace PI.VolStabW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

instance Rm_sf (S : Finset ι) : SigmaFinite (Rm m L S) := by unfold Rm; infer_instance

lemma Qm_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  unfold Qm
  split_ifs with hh
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (hh i.1 i.2)
    have hP : ∀ j : {i // i ∉ S}, Integrable (g j.1) (Pn m L j.1) := fun j =>
      ((hg j.1).restrict).smul_measure (ENNReal.inv_ne_top.2 (hh j.1 j.2).1)
    let F : (∀ j : T', W j.1.1) → ℂ := fun y => ∏ j : T', g j.1.1 (y j)
    have hpi : Integrable F (Measure.pi (fun j : T' => Pn m L j.1.1)) :=
      Integrable.fintype_prod_dep (fun j => hP j.1)
    have hre : (fun z : (∀ j : {i // i ∉ S}, W j.1) => ∏ j ∈ T', g j.1 (z j)) =
        fun z => F (T'.restrict z) := by
      funext z
      exact (Finset.prod_coe_sort T' (fun j => g j.1 (z j))).symm
    have hmap := Measure.infinitePi_map_restrict (μ := fun j : {i // i ∉ S} => Pn m L j.1) (I := T')
    have hpi' : Integrable F ((Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1).map
        T'.restrict) := by rw [hmap]; exact hpi
    have hint : Integrable (fun z => F (T'.restrict z))
        (Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1) :=
      (integrable_map_measure hpi'.aestronglyMeasurable
        (Finset.measurable_restrict _).aemeasurable).1 hpi'
    rw [hre]
    refine ⟨hint.smul_measure_nnreal, ?_⟩
    rw [integral_smul_nnreal_measure,
      integral_restrict_infinitePi (fun j : {i // i ∉ S} => Pn m L j.1) hpi.aestronglyMeasurable]
    simp only [F]
    rw [integral_fintype_prod_eq_prod]
    simp only [Pn, integral_smul_measure]
    rw [Finset.prod_coe_sort T' (fun j => ((m j.1 (L j.1))⁻¹.toReal • ∫ w, g j.1 w ∂(m j.1).restrict (L j.1))),
      hT', Finset.prod_subtype_eq_prod_filter (f := fun i => ((m i (L i))⁻¹.toReal • ∫ w, g i w ∂(m i).restrict (L i))),
      ← Finset.sdiff_eq_filter, tl_split hT hST]
    have hmu : ∀ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i) = ∫ w, g i w ∂(m i).restrict (L i) := by
      intro i hi
      rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [Finset.prod_congr rfl hmu]
    have hone : (∏ i ∈ T \ S, ((am m L i : ℝ) : ℂ)) * (∏ i ∈ T \ S, (((m i (L i))⁻¹.toReal : ℝ) : ℂ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one (fun i hi => ?_)
      have h1 := hh i (Finset.mem_sdiff.1 hi).2
      rw [← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_inv,
        mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h1.1, h1.2⟩), Complex.ofReal_one]
    simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod,
      Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
    linear_combination (((tl m L T : ℝ) : ℂ) * ∏ i ∈ T \ S, ∫ w, g i w ∂(m i).restrict (L i)) * hone
  · push_neg at hh
    obtain ⟨i, hiS, hi⟩ := hh
    have h0 : m i (L i) = 0 := by
      by_contra h; exact hfin i (hi h)
    refine ⟨integrable_zero_measure, ?_⟩
    rw [integral_zero_measure]
    by_cases hiT : i ∈ T
    · rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hiT, hiS⟩), zero_mul]
      rw [mu, if_neg hiS, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    · rw [tl_zero hT hiT (by simp [am, h0])]
      simp

lemma kap_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  have hfun : ∀ p, (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ((eS S).symm p) =
      (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) := by
    intro p
    simp only
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ S)]
    congr 1
    · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST, ← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [eS_symm_apply, dif_pos i.2]
    · rw [← Finset.prod_subtype_eq_prod_filter]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [eS_symm_apply, dif_neg j.2]
  have hR : Integrable (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (Rm m L S) := by
    unfold Rm; exact Integrable.fintype_prod_dep (fun i => (hg i.1).restrict)
  obtain ⟨hQi, hQ⟩ := Qm_integral hfin hT hST g hg
  rw [← hT'] at hQi hQ
  have hcomp : (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm =
      fun p => (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) :=
    funext hfun
  refine ⟨?_, ?_⟩
  · unfold kap
    rw [integrable_map_equiv, hcomp]
    exact Integrable.mul_prod (μ := Rm m L S) (ν := Qm m L S)
      (f := fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (g := fun z => ∏ j ∈ T', g j.1 (z j)) hR hQi
  · unfold kap
    rw [integral_map_equiv]
    refine (integral_congr_ae (ae_of_all _ hfun)).trans ?_
    rw [integral_prod_mul (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (fun z : (∀ i : {i // i ∉ S}, W i) => ∏ j ∈ T', g j.1 (z j)), hQ, Rm, integral_fintype_prod_eq_prod,
      ← Finset.prod_sdiff hST]
    have hS : ∏ i : {i // i ∈ S}, ∫ w, g i.1 w ∂(m i.1).restrict (L i.1)ᶜ =
        ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i) := by
      rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [mu, if_pos i.2]
    rw [hS]
    ring

end PI.VolStabW.RPA
end
end

section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Filter Finset PI.VolStabW.RPA
open scoped NNReal ENNReal

theorem rpAbs_holds : RPAbs := by
  intro ι _ W _ m _ L hLm hfin hT
  classical
  have hT' : TailH m L := hT
  refine ⟨Measure.sum (kap m L), inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    have := kap_ae (m := m) (L := L) hLm S
    rw [ae_iff] at this
    refine measure_mono_null (fun x hx => ?_) this
    intro hgood
    apply hx
    rw [Filter.eventually_cofinite]
    refine (S.finite_toSet).subset (fun i hi => ?_)
    by_contra hiS
    exact hi ((hgood i).2 hiS)
  · intro i C hC hC0
    rw [Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
    intro S
    refine kap_eval_null (m := m) (L := L) (S := S) (A := Cᶜ) hC.compl ?_
    unfold mu
    split_ifs <;> exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hC0.le)
  · intro f hf hcof
    have hfin0 := Filter.eventually_cofinite.1 hcof
    set S0 := hfin0.toFinset with hS0def
    have hS0 : ∀ i, i ∉ S0 → f i = (L i).indicator 1 := fun i hi => by
      by_contra h; exact hi (hfin0.mem_toFinset.2 h)
    set G : (∀ i, W i) → ℂ := fun x => ∏ i ∈ S0, f i (x i) with hG
    have hae : ∀ S : Finset ι, (fun x => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => if S ⊆ S0 then G x else 0 := by
      intro S
      filter_upwards [kap_ae (m := m) (L := L) hLm S] with x hx
      have hsupp : Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ S0) := by
        intro i hi
        by_contra hn
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hn
        apply hi
        simp only [hS0 i hn.2, Set.indicator_of_mem ((hx i).2 hn.1), Pi.one_apply]
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
      by_cases hsub : S ⊆ S0
      · rw [if_pos hsub, Finset.union_eq_right.2 hsub]
      · rw [if_neg hsub]
        obtain ⟨j, hjS, hj0⟩ := Finset.not_subset.1 hsub
        refine Finset.prod_eq_zero (Finset.mem_union_left _ hjS) ?_
        simp [hS0 j hj0, (hx j).1 hjS]
    have hK : ∀ S ⊆ S0, Integrable G (kap m L S) ∧
        ∫ x, G x ∂kap m L S = (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) :=
      fun S hS => kap_integral hfin hT' hS f hf
    have hIntS : ∀ S, Integrable (fun x => ∏ᶠ i, f i (x i)) (kap m L S) := by
      intro S
      refine Integrable.congr ?_ (hae S).symm
      by_cases hs : S ⊆ S0
      · simp only [hs, if_true]; exact (hK S hs).1
      · simp only [hs, if_false]; exact integrable_zero _ _ _
    have hzero : ∀ S, S ∉ S0.powerset → ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S = 0 ∧
        ∫ x, ‖∏ᶠ i, f i (x i)‖ ∂kap m L S = 0 := by
      intro S hS
      have hs : ¬ S ⊆ S0 := fun h => hS (Finset.mem_powerset.2 h)
      refine ⟨?_, ?_⟩
      · rw [integral_congr_ae (hae S)]; simp [hs]
      · refine (integral_congr_ae ((hae S).fun_comp norm)).trans ?_
        simp [hs, Function.comp_def]
    have hint : Integrable (fun x => ∏ᶠ i, f i (x i)) (Measure.sum (kap m L)) :=
      integrable_sum_measure hIntS (summable_of_ne_finset_zero (s := S0.powerset)
        (fun S hS => (hzero S hS).2))
    refine ⟨hint, ?_⟩
    rw [integral_sum_measure hint, tsum_eq_sum (s := S0.powerset) (fun S hS => (hzero S hS).1)]
    have hsumS : ∑ S ∈ S0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        ∑ S ∈ S0.powerset, (∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i)) * (tl m L S0 : ℂ) := by
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [integral_congr_ae (hae S)]
      simp only [hs, if_true]
      exact (hK S hs).2
    rw [hsumS, ← Finset.sum_mul]
    have hsplit : ∀ i, ∫ w, f i w ∂(m i) =
        (∫ w, f i w ∂(m i).restrict (L i)ᶜ) + ∫ w, f i w ∂(m i).restrict (L i) := fun i => by
      rw [add_comm]; exact (integral_add_compl (hLm i) (hf i)).symm
    have hprodadd : ∑ S ∈ S0.powerset, ∏ i ∈ S0, ∫ w, f i w ∂(mu m L S i) =
        ∏ i ∈ S0, ∫ w, f i w ∂(m i) := by
      rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_add]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have hs := Finset.mem_powerset.1 hS
      rw [← Finset.prod_sdiff hs, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_pos hi]
      · refine Finset.prod_congr rfl (fun i hi => ?_); rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [hprodadd]
    have h1 : HasProd (fun i => (((({i | i ∉ S0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        (((tl m L S0 : ℝ≥0) : ℝ) : ℂ) := by
      have := (hasProd_ind hT' S0).map
        (((Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom).comp (NNReal.toRealHom.toMonoidHom))
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
      exact this
    have h2 : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
        (∏ i ∈ S0, ∫ w, f i w ∂(m i)) := by
      have : HasProd (fun i => if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)
          (∏ i ∈ S0, (if i ∈ S0 then ∫ w, f i w ∂(m i) else 1)) :=
        hasProd_prod_of_ne_finset_one (fun b hb => if_neg hb)
      convert this using 1
      exact (Finset.prod_congr rfl (fun i hi => if_pos hi)).symm
    have h3 := h2.mul h1
    convert h3 using 1
    funext i
    by_cases hi : i ∈ S0
    · simp [hi]
    · have hmem : i ∈ ({i | i ∉ S0} : Set ι) := hi
      rw [if_neg hi, one_mul, Set.mulIndicator_of_mem hmem, hS0 i hi,
        integral_indicator (hLm i)]
      simp [am, Measure.real]
      exact (ENNReal.coe_toNNReal_eq_toReal _).symm

end PI.VolStabW
end
end
