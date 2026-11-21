import Mathlib
import Formalism.PeriodIntegrals.BesselPeriodGGP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.FormalDegreeHaarQuotient
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DecreasingNodeGaps

section
namespace GlobalTheory.Proof.NodeGapNoncompact

open PI.BesselPeriodGGP GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps

theorem lam_eq (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    lam48 k r v b = param r k hk v b := by
  funext s
  unfold lam48
  by_cases h : s.val < k - 1
  · rw [dif_pos h]
    exact (param_cloud r k hk v b ⟨s.val, h⟩).symm
  · rw [dif_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, param_node]

theorem sign_eq (k r : ℕ) (hk : 1 ≤ k) : eps48 k r = sign r k hk := by
  funext s
  unfold eps48
  by_cases h : s.val < k - 1
  · rw [if_pos h]
    exact (sign_cloud r k hk ⟨s.val, h⟩).symm
  · rw [if_neg h]
    have hs : s = nodeIdx r k hk ⟨s.val - (k - 1), by have := s.isLt; omega⟩ := by
      apply Fin.ext
      simp only [nodeIdx]
      omega
    conv_rhs => rw [hs, sign_node]
    simp only [Nat.even_iff]

theorem interlace_iff (k r : ℕ) (hk : 1 ≤ k) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) :
    InterlacingCondition k r u v b ↔ Interlaces r k (param r k hk v b) u := by
  have hc : ∀ (i : ℕ) (hi : i < k - 1) (hi' : i < 2 * r + k + 1),
      param r k hk v b ⟨i, hi'⟩ = v ⟨i, hi⟩ := fun i hi _ => param_cloud r k hk v b ⟨i, hi⟩
  have hn : ∀ (hi' : k - 1 < 2 * r + k + 1),
      param r k hk v b ⟨k - 1, hi'⟩ = -b ⟨0, by omega⟩ :=
    fun _ => param_node r k hk v b ⟨0, by omega⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_cases h : i.val < k - 1
      · rw [hc i.val h]
        exact (h1 ⟨i.val, h⟩).1
      · obtain ⟨i, hi⟩ := i
        obtain rfl : i = k - 1 := by simp only at h; omega
        rw [hn]
        exact h2 hk
    · rw [hc i (by omega)]
      exact (h1 ⟨i, by omega⟩).2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨?_, ?_⟩, fun h => ?_⟩
    · have := h1 ⟨i.val, by have := i.isLt; omega⟩
      rwa [hc i.val i.isLt] at this
    · have := h2 i.val (by have := i.isLt; omega)
      rwa [hc i.val i.isLt] at this
    · have := h1 ⟨k - 1, by omega⟩
      rwa [hn] at this


theorem gap_iff (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) :
    LowGapGe h r b ↔ NodeGapGe r b h := by
  constructor
  · intro H i hi
    have := H ⟨i, by omega⟩ hi
    simp only at this
    linarith
  · intro H j hj
    have := H j.val hj
    simp only [Fin.eta] at this
    linarith



theorem isHCParam_iff (k r : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) :
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ↔
      IsDecreasing r k hk v b ∧ IsShiftedIntegral (param r k hk v b) := by
  unfold Formalism.QuantumDeterminants.IsHCParam IsDecreasing IsShiftedIntegral
  rw [lam_eq k r hk]
  refine and_congr Iff.rfl (forall_congr' fun s => exists_congr fun z => ?_)
  constructor <;> intro h <;> linarith



end GlobalTheory.Proof.NodeGapNoncompact
end

section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselPeriodCompare

open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open Formalism.FourierDecayAlt.B2 (IsClosedSubgroup mulM invM)
open Formalism.FourierDecayAlt.P.B2x1
open GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient (Mat leviW IsClosedMatGroup)

variable {k r : ℕ}


theorem exists_pos_lt_top {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (h : μ ≠ 0) : ∃ t : Set X, μ t ≠ 0 ∧ μ t ≠ ⊤ := by
  have h0 : (0 : ℝ≥0∞) < μ Set.univ := by
    rw [pos_iff_ne_zero]; exact fun h' => h (Measure.measure_univ_eq_zero.mp h')
  obtain ⟨t, -, -, h1, h2⟩ := Measure.exists_subset_measure_lt_top MeasurableSet.univ h0
  exact ⟨t, h1.ne', h2.ne⟩

theorem haar_unique {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨m1, m2, m3, m4⟩ := hμ
  obtain ⟨n1, n2, n3, n4⟩ := hν
  have em : (pull hU μ).map inc = μ := map_pull μ m3
  have en : (pull hU ν).map inc = ν := map_pull ν n3
  have : (pull hU μ).IsMulLeftInvariant := pull_left μ m4
  have : (pull hU ν).IsMulLeftInvariant := pull_left ν n4
  have : SigmaFinite (pull hU μ) :=
    SigmaFinite.of_map _ inc_memb.measurable.aemeasurable (by rw [em]; exact m1)
  have : SigmaFinite (pull hU ν) :=
    SigmaFinite.of_map _ inc_memb.measurable.aemeasurable (by rw [en]; exact n1)
  obtain ⟨s, s0, s1⟩ := exists_pos_lt_top (pull hU ν) (by
    intro h; apply n2; rw [← en, h, Measure.map_zero])
  have e := measure_eq_div_smul (pull hU μ) (pull hU ν) s0 s1
  generalize pull hU μ s / pull hU ν s = c at e
  have e' : μ = c • ν := by rw [← em, e, Measure.map_smul, en]
  refine ⟨c, ?_, ?_, e'⟩
  · rintro rfl
    exact m2 (by rw [e', zero_smul])
  · rintro rfl
    obtain ⟨t, t0, t1⟩ := exists_pos_lt_top μ m2
    rw [e', Measure.smul_apply, smul_eq_mul] at t0 t1
    by_cases h : ν t = 0
    · exact t0 (by rw [h, mul_zero])
    · exact t1 (ENNReal.top_mul h)

theorem haar_of_compact {U : Set (Mat k r)} (hU : IsClosed U) {μ : Measure (Mt k r)}
    (hμ : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ) : PI.BesselPeriodGGP.IsHaarOn U μ := by
  obtain ⟨m1, m2, m3, m4⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hle : μ K ≤ μ (K ∩ amb U) := by
      refine measure_mono_ae ?_
      have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ U := by rw [ae_iff]; exact m1
      filter_upwards [hae] with x hx hK using ⟨hK, hx⟩
    exact lt_of_le_of_lt hle (m3 _ (hK.inter_right hU) fun x hx => hx.2)
  exact ⟨inferInstance, m4, m1, m2⟩

theorem exists_haar {U : Set (Mat k r)} (hU : IsClosedSubgroup U) :
    ∃ μ, GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ := by
  let m : Measure (Gp U hU) := Measure.haar
  have hm : Measurable (inc : Gp U hU → Mt k r) := inc_memb.measurable
  refine ⟨m.map inc, ?_, ?_, ?_, ?_⟩
  · rw [inc_memb.map_apply]
    have : (inc : Gp U hU → Mt k r) ⁻¹' {x | Matrix.of x ∉ U} = ∅ := by
      ext x; simpa using inc_mem x
    rw [this, measure_empty]
  · intro a ha
    let g : Gp U hU := ⟨Matrix.of.symm a, ha⟩
    rw [Measure.map_map (lmulM_cont a).measurable hm]
    have : (lmulM a ∘ inc : Gp U hU → Mt k r) = inc ∘ (fun x => g * x) := rfl
    rw [this, ← Measure.map_map hm (continuous_const_mul g).measurable, map_mul_left_eq_self]
  · intro C hC _
    rw [inc_memb.map_apply]
    exact (inc_closedEmb.isCompact_preimage hC).measure_lt_top
  · intro h
    rw [Measure.map_eq_zero_iff hm.aemeasurable] at h
    exact NeZero.ne m h

theorem isHaarOn_iff {U : Set (Mat k r)} (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) :
    PI.BesselPeriodGGP.IsHaarOn U μ ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn U μ := by
  refine ⟨fun h => ?_, haar_of_compact hU.closed⟩
  obtain ⟨ν, hν⟩ := exists_haar hU
  obtain ⟨c, -, c1, e⟩ := haar_unique hU h (haar_of_compact hU.closed hν)
  refine ⟨h.2.2.1, h.2.2.2, fun C hC hCU => ?_, h.2.1⟩
  rw [e, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top c1.lt_top (hν.2.2.1 C hC hCU)



theorem psiGen_eq : @PI.BesselPeriodGGP.psiGen = @PI.BesselMapUniq.psiGen := rfl


theorem symmetricMeasure_l2Norm_eq_resolutionL2 {Wp : Type*} [NormedAddCommGroup Wp]
    (ν : Measure (Mt k r)) (φ : Mat k r → Wp) :
    PI.BesselPeriodGGP.l2SG ν φ = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.sectionL2NormSq ν φ := rfl

theorem fdeg_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure (Mt k r))
    (σ : Mat k r → (H →L[ℂ] H)) (w : H)
    (hm : AEStronglyMeasurable (fun x : Mt k r => ⟪w, σ (Matrix.of x) w⟫_ℂ) μ) :
    PI.BesselPeriodGGP.fdegH μ σ w = GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt μ σ w := by
  unfold PI.BesselPeriodGGP.fdegH GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.formalDegreeAt GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.coefNormSq
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hm.norm.pow 2)]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]



def uinv (k r : ℕ) (h : Mat k r) : Mat k r := Hpk k r * hᴴ * Hpk k r

theorem uinv_eq {h : Mat k r} (hh : h ∈ UH (Hpk k r)) : uinv k r h = h⁻¹ := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh
  refine (Matrix.inv_eq_left_inv ?_).symm
  calc uinv k r h * h = Hpk k r * (hᴴ * Hpk k r * h) := by simp only [uinv, Matrix.mul_assoc]
    _ = 1 := by rw [hU, (Formalism.QuantumDeterminants.hpkFacts k r).2.1]

theorem continuous_uinv : Continuous (uinv k r) :=
  (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

theorem continuous_leviW : Continuous (leviW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold leviW
  split_ifs
  · exact continuous_id.matrix_elem i j
  · exact continuous_const
  · exact continuous_const

def split (k r : ℕ) (s : Mt k r) : Mt k r × Mt k r :=
  (leviW k r (Matrix.of s), uinv k r (leviW k r (Matrix.of s)) * Matrix.of s)

theorem continuous_split : Continuous (split k r) :=
  (continuous_leviW (k := k) (r := r)).prodMk
    (((continuous_uinv (k := k) (r := r)).comp continuous_leviW).matrix_mul continuous_id)

theorem split_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : split k r (h * n) = (h, n) := by
  have e : leviW k r (h * n) = h := GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.leviW_mul hh hn
  refine Prod.ext e ?_
  show uinv k r (leviW k r (h * n)) * (h * n) = n
  rw [e, uinv_eq hh.1, Matrix.nonsing_inv_mul_cancel_left _ _
    ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit h hh)]

theorem closedS {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : IsClosedSubgroup (Sset k r z) := by
  obtain ⟨h1, h2, h3⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  have hW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hN := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rintro a ⟨h, hh, n, hn, rfl⟩
    rw [Matrix.det_mul]
    exact (hW.unit h hh).mul (hN.unit n hn)
  · have e : Sset k r z = split k r ⁻¹' (amb (UWset k r z) ×ˢ amb (Nset k r)) := by
      ext s
      constructor
      · rintro ⟨h, hh, n, hn, rfl⟩
        show split k r (h * n) ∈ amb (UWset k r z) ×ˢ amb (Nset k r)
        rw [split_mul hh hn]
        exact ⟨hh, hn⟩
      · rintro ⟨hh, hn⟩
        have hh' : leviW k r s ∈ UWset k r z := hh
        refine ⟨_, hh', uinv k r (leviW k r s) * s, hn, ?_⟩
        rw [uinv_eq hh'.1, Matrix.mul_nonsing_inv_cancel_left _ _ (hW.unit _ hh')]
    rw [e]
    exact ((amb_closed hW).prod (amb_closed hN)).preimage continuous_split

theorem ae_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem map_split {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    ((μW.prod μN).map mulM).map (split k r) = μW.prod μN := by
  rw [Measure.map_map continuous_split.measurable mulM_cont.measurable]
  conv_rhs => rw [← Measure.map_id (μ := μW.prod μN)]
  refine Measure.map_congr ?_
  filter_upwards [ae_prod hW hN] with p hp
  exact split_mul hp.1 hp.2

theorem haar_prod {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) :
    PI.BesselPeriodGGP.IsHaarOn (Sset k r z) ((μW.prod μN).map mulM) := by
  have := hW.1
  have := hN.1
  have cW := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SigmaFinite.of_map _ continuous_split.measurable.aemeasurable
      (by rw [map_split hW hN]; infer_instance)
  · intro h
    rw [Measure.map_eq_zero_iff hm.aemeasurable] at h
    have h' := congrArg (fun m : Measure (Mt k r × Mt k r) => m (Set.univ ×ˢ Set.univ)) h
    simp only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      Measure.measure_univ_eq_zero] at h'
    exact h'.elim hW.2.1 hN.2.1
  · rw [← ae_iff]
    refine (ae_map_iff hm.aemeasurable (amb_closed (closedS hz)).measurableSet).mpr ?_
    filter_upwards [ae_prod hW hN] with p hp
    exact ⟨_, hp.1, _, hp.2, rfl⟩
  · rintro s ⟨h, hh, n, hn, rfl⟩
    let g : Mt k r → Mt k r → Mt k r := fun a x => lmulM (uinv k r (Matrix.of a) * n * Matrix.of a) x
    have hg : Continuous (Function.uncurry g) :=
      ((((continuous_uinv (k := k) (r := r)).comp continuous_fst).matrix_mul continuous_const).matrix_mul
        continuous_fst).matrix_mul continuous_snd
    have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
    have hp : MeasurePreserving (fun p : Mt k r × Mt k r => (lmulM h p.1, g p.1 p.2))
        (μW.prod μN) (μW.prod μN) := by
      refine MeasurePreserving.skew_product ⟨(lmulM_cont h).measurable, hW.2.2.2 h hh⟩ hg.measurable ?_
      filter_upwards [h1] with a ha
      refine hN.2.2.2 _ ?_
      have := (Formalism.QuantumDeterminants.uWNormal k r z hz _ (cW.inv_mem _ ha) n hn).1
      rwa [Matrix.nonsing_inv_nonsing_inv _ (cW.unit _ ha), ← uinv_eq ha.1] at this
    conv_rhs => rw [← hp.map_eq]
    rw [Measure.map_map (lmulM_cont _).measurable hm, Measure.map_map hm hp.measurable]
    refine Measure.map_congr ?_
    filter_upwards [ae_prod hW hN] with p hp
    show h * n * (Matrix.of p.1 * Matrix.of p.2) =
      h * Matrix.of p.1 * (uinv k r (Matrix.of p.1) * n * Matrix.of p.1 * Matrix.of p.2)
    rw [uinv_eq hp.1.1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (cW.unit _ hp.1)]

theorem integral_map_of_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN) (f : Mt k r → E) :
    ∫ s, f s ∂((μW.prod μN).map mulM) = ∫ p, f (mulM p) ∂(μW.prod μN) := by
  have hm : Measurable (mulM : Mt k r × Mt k r → Mt k r) := mulM_cont.measurable
  by_cases hf : AEStronglyMeasurable f ((μW.prod μN).map mulM)
  · exact integral_map hm.aemeasurable hf
  · rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable]
    intro h
    apply hf
    rw [← map_split hW hN] at h
    refine (h.comp_measurable continuous_split.measurable).congr ?_
    have hc : Continuous fun s : Mt k r => mulM (split k r s) := mulM_cont.comp continuous_split
    have : ∀ᵐ s ∂((μW.prod μN).map mulM), mulM (split k r s) = s := by
      refine (ae_map_iff hm.aemeasurable (isClosed_eq hc continuous_id).measurableSet).mpr ?_
      filter_upwards [ae_prod hW hN] with p hp
      exact congrArg mulM (split_mul hp.1 hp.2)
    filter_upwards [this] with s hs
    exact congrArg f hs

theorem star_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (n : Mat k r) :
    star (PI.BesselPeriodGGP.psiGen k r z c n) = (PI.BesselMapUniq.psiGen k r z c n)⁻¹ := by
  rw [psiGen_eq]
  unfold PI.BesselMapUniq.psiGen
  rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_mul]

theorem period_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW μN μS : Measure (Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.IsHaarOn (Sset k r z) μS) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (c : Fin r → ℂ)
      (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (w v : H),
      GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period k r z c σ π μS w v =
        t • ∫ p : Mt k r × Mt k r,
          (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ *
            star (PI.BesselPeriodGGP.psiGen k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
          ∂(μW.prod μN) := by
  obtain ⟨t, t0, t1, e⟩ := haar_unique (closedS hz) (haar_of_compact (closedS hz).closed hS)
    (haar_prod hz hW hN)
  refine ⟨t.toReal, ENNReal.toReal_pos t0 t1, fun H _ _ Wp _ _ c σ π w v => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period
  rw [e, integral_smul_measure, integral_map_of_split hW hN]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_prod hW hN] with p hp
  have h := (GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.twist_mul c π hp.1 hp.2
    ((Formalism.FourierDecayAlt.P.B2x3.closedW k r z).unit _ hp.1)).2
  rw [star_psiGen, ← smul_smul, ← h]
  rfl




end GlobalTheory.BesselPeriodCompare

end
end
