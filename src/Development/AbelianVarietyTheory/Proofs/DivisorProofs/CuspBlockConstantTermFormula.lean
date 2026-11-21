import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentRadicalEqLeviMulUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAlongSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasure
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono

section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_normal_subgroup_fibration : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  first | exact @GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo | exact GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo | (intros; apply GlobalTheory.Cusp.Shear.isHaarMeasure_map_prodHomeo <;> assumption)
end

section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_fibration_section_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  first | exact @GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | exact GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod | (intros; apply GlobalTheory.Cusp.Shear.isFundamentalDomain_image_prod <;> assumption)
end

section
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem exists_measurable_addSection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N : Subgroup G) [DiscreteTopology Γ]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) (s : V → G) (π : N → V), Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) →
    (∀ (a : N) (v : V), (a : G) = s v → π a = v) → (∀ v ∈ Λ, s v ∈ Γ) →
    ∃ B : Set V, MeasurableSet B ∧ ∀ v : V, ∃! w : Λ, (w : V) + v ∈ B := by
  intro G _ _ _ _ _ _ Γ N _ V _ _ _ _ Λ s π hsc hmul hs hπs hsΓ
  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hπs' : ∀ v, π (s' v) = v := fun v => hπs _ v rfl
  have hs'add : ∀ v w, s' (v + w) = s' v * s' w := fun v w => Subtype.ext (hmul v w)
  have hs0 : s' 0 = 1 := by
    have h := hs'add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)

  let H : Subgroup N :=
    { carrier := {n | n = s' (π n) ∧ π n ∈ Λ}
      one_mem' := by
        have h1 : π 1 = 0 := by rw [← hs0, hπs']
        exact ⟨by rw [h1, hs0], by rw [h1]; exact Λ.zero_mem⟩
      mul_mem' := fun {a b} ha hb => by
        have e : a * b = s' (π a + π b) := by rw [hs'add, ← ha.1, ← hb.1]
        have hp : π (a * b) = π a + π b := by rw [e, hπs']
        exact ⟨by rw [hp]; exact e, by rw [hp]; exact Λ.add_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => by
        have h1 : s' (π a) * s' (-π a) = 1 := by rw [← hs'add, add_neg_cancel, hs0]
        have e : a⁻¹ = s' (-π a) :=
          (congrArg (·⁻¹) ha.1).trans (eq_inv_of_mul_eq_one_right h1).symm
        have hp : π a⁻¹ = -π a := by rw [e, hπs']
        exact ⟨by rw [hp]; exact e, by rw [hp]; exact Λ.neg_mem ha.2⟩ }
  have hH : ∀ h : H, ((h : N) : G) ∈ Γ := fun h => by
    have e : ((h : N) : G) = s (π h) := congrArg Subtype.val h.2.1
    rw [e]; exact hsΓ _ h.2.2
  haveI : DiscreteTopology H :=
    .of_continuous_injective (f := fun h : H => (⟨((h : N) : G), hH h⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      fun a b e => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) e))
  refine ⟨s' ⁻¹' stdDom H, (hsc.subtype_mk hs).measurable (measurableSet_stdDom H), fun v => ?_⟩
  obtain ⟨h, hh, hu⟩ := existsUnique_stdDom H (s' v)
  refine ⟨⟨π h, h.2.2⟩, ?_, fun w hw => ?_⟩
  · show s' (π h + v) ∈ stdDom H
    rw [hs'add, ← h.2.1]
    exact hh
  · have hmem : s' w ∈ H := ⟨by rw [hπs'], by rw [hπs']; exact w.2⟩
    have e := hu ⟨s' w, hmem⟩ (by
      show s' w * s' v ∈ stdDom H
      rw [← hs'add]
      exact hw)
    apply Subtype.ext
    show (w : V) = π h
    rw [← e]
    exact (hπs' w).symm

theorem integral_section_eq_constTermOn : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  intro G _ _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ Λ s π hsc hmul hs hπc hπmul hπs hker hsΓ hπΓ
    φ hφ hφc hN' μ 𝓕 hμ h𝓕 x

  let s' : V → N := fun v => ⟨s v, hs v⟩
  have hs'c : Continuous s' := hsc.subtype_mk _
  have hleft : Function.LeftInverse π s' := fun v => hπs _ v rfl
  have hemb : Topology.IsEmbedding s' := hleft.isEmbedding hπc hs'c
  haveI : SecondCountableTopology V := hemb.secondCountableTopology
  haveI : T2Space V := hemb.t2Space
  haveI : Countable Λ := Function.Injective.countable (f := fun w : Λ => (⟨s w, hsΓ _ w.2⟩ : Γ)) fun a b h =>
    Subtype.ext (hleft.injective (Subtype.ext (congrArg Subtype.val h : s a = s b)))
  let e := prodHomeo hle hs hsc hπc hπmul hπs hker
  let ν : Measure N := ((Measure.haar : Measure N').prod μ).map e
  haveI : ν.IsHaarMeasure := GlobalTheory.T.cocompact_normal_subgroup_fibration G Γ N N' hle hn hc hc' V s π hs hsc hπc hπmul hπs hker hmul μ hμ
  obtain ⟨B, hBm, hB⟩ := exists_measurable_addSection G Γ N V Λ s π hsc hmul hs hπs hsΓ
  let A := stdDom (Γ.subgroupOf N')
  have hAm : MeasurableSet A := measurableSet_stdDom _
  have hD : IsFundamentalDomain (Γ.subgroupOf N) (e '' (A ×ˢ B)) ν :=
    GlobalTheory.T.cocompact_fibration_section_measure G Γ N N' hle hn V Λ s π hs hsc hπc hπmul hπs hker hmul hsΓ hπΓ A B hAm hBm
      (existsUnique_stdDom _) hB ν
  have hep : MeasurePreserving e ((Measure.haar : Measure N').prod μ) ν := ⟨e.continuous.measurable, rfl⟩
  have hemb' : MeasurableEmbedding e := e.toMeasurableEquiv.measurableEmbedding

  have hI : ∫ n in e '' (A ×ˢ B), φ (n * x) ∂ν =
      (Measure.haar : Measure N').real A • ∫ v in B, φ (s v * x) ∂μ := by
    rw [hep.setIntegral_image_emb hemb', ← Measure.prod_restrict]
    have h1 : ∀ z : N' × V, φ ((e z : G) * x) = φ (s z.2 * x) := fun z => by
      rw [prodHomeo_apply, mul_assoc]; exact hN' _ z.1.2 _
    simp only [h1]
    rw [integral_fun_snd (fun v => φ (s v * x)), measureReal_restrict_apply_univ]
  have hM : ν (e '' (A ×ˢ B)) = Measure.haar A * μ B := by
    change ((Measure.haar : Measure N').prod μ).map e _ = _
    rw [hemb'.map_apply, e.preimage_image, Measure.prod_prod]
  have hA0 : (Measure.haar : Measure N') A ≠ 0 := (isFundamentalDomain_stdDom _ _).measure_ne_zero (NeZero.ne _)
  have hAt : (Measure.haar : Measure N') A ≠ ⊤ := hc'.measure_ne_top (isFundamentalDomain_stdDom _ _)
  have hDt := hc.measure_ne_top hD
  have hD0 := hD.measure_ne_zero (NeZero.ne ν)
  rw [hM] at hDt hD0
  have hBt : μ B ≠ ⊤ := fun h => hDt (by rw [h, ENNReal.mul_top hA0])
  have hB0 : μ B ≠ 0 := fun h => hD0 (by rw [h, mul_zero])

  have hBF : IsAddFundamentalDomain Λ B μ := .mk' hBm.nullMeasurableSet fun v => by
    simpa [AddSubgroup.vadd_def, vadd_eq_add] using hB v
  have hf : ∀ (w : Λ) (v : V), φ (s ((w : V) + v) * x) = φ (s v * x) := fun w v => by
    rw [hmul, mul_assoc]; exact hφ _ (hsΓ _ w.2) _
  rw [h𝓕.setIntegral_eq hBF (fun w v => hf w v), measureReal_def, h𝓕.measure_eq hBF, constTermOn_eq hD hφ x, hI,
    measureReal_def, hM, measureReal_def, ENNReal.toReal_mul, smul_smul, smul_smul]
  have ha : ((Measure.haar : Measure N') A).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hA0, hAt⟩
  have hb : (μ B).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hB0, hBt⟩
  rw [show (μ B).toReal * (((Measure.haar : Measure N') A).toReal * (μ B).toReal)⁻¹ *
      ((Measure.haar : Measure N') A).toReal = 1 by field_simp, one_smul]

end GlobalTheory.Cusp.Shear

end
end

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_normal_subgroup_descent_invariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  atlas_forward_decl GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix GlobalTheory.StdPar
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.CuspUnip

theorem sub_mem_span {A : Type} [CommRing A] {n r d : ℕ} {X Y : Matrix (Fin n) (Fin r) A} {L K : Matrix (Fin r) (Fin n) A}
    (e : Fin d → Fin r) (P Q : Matrix (Fin d) (Fin d) A) (r' : ℕ)
    (hP : ∀ a b : Fin d, ¬ (a.val < r' ∧ r' ≤ b.val) → P a b = 0) {I : Set (Fin r)} {y : Fin n → A}
    (hL : ∀ a, (L *ᵥ y) (e a) = 0)
    (hI : (∀ b : Fin d, r' ≤ b.val → (K *ᵥ y) (e b) = 0) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) :
    (1 + X.submatrix id e * P * K.submatrix e id + Y.submatrix id e * Q * L.submatrix e id) *ᵥ y - y ∈
      Submodule.span A ((fun i => Xᵀ i) '' I) := by
  have h1 : (fun a => (L *ᵥ y) (e a)) = 0 := funext hL
  rw [GlobalTheory.BlockForms.Norm.blk_mulVec, h1, mulVec_zero, mulVec_zero, add_zero, add_sub_cancel_left]
  rcases hI with hI | hI
  · have h2 : P *ᵥ (fun a => (K *ᵥ y) (e a)) = 0 := funext fun a => by
      simp only [mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : r' ≤ b.val
      · change P a b * (K *ᵥ y) (e b) = 0
        rw [hI b hb, mul_zero]
      · rw [hP a b (fun h' => hb h'.2), zero_mul]
    rw [h2, mulVec_zero]
    exact zero_mem _
  · rw [mulVec_eq_sum]
    refine sum_mem fun a _ => ?_
    rw [op_smul_eq_smul]
    by_cases ha : a.val < r'
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e a, hI a ha, rfl⟩)
    · have : (P *ᵥ fun a => (K *ᵥ y) (e a)) a = 0 := by
        simp only [mulVec, dotProduct]
        exact Finset.sum_eq_zero fun b _ => by rw [hP a b (fun h' => ha h'.1), zero_mul]
      rw [this, zero_smul]
      exact zero_mem _

theorem blockEmb_unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∀ x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E, ι (GlobalTheory.CuspRep.unip x) ∈ GlobalTheory.StdPar.unip σ J Xf (insert k S) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, _, _, _, hΦ, hι⟩ hS hk0 _ r' hr0 hrd k hk x
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  obtain ⟨k0, hk0S, hk0⟩ := hk0
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hLX : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [hm, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, GlobalTheory.StdPar.yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hP : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (a b : Fin d), ¬ (a.val < r' ∧ r' ≤ b.val) →
      ((GlobalTheory.CuspRep.unip x).1.map Φ.symm - 1) a b = 0 := by
    intro x a b hab
    rw [Matrix.sub_apply, Matrix.map_apply]
    change Φ.symm ((1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) a b) - _ = 0
    rw [Matrix.add_apply, map_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dif_neg hab, map_zero, add_zero]
    by_cases hab' : a = b <;> simp [Matrix.one_apply, hab']
  have core : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) {I : Set (Fin r)} {y : Fin n → AF F ⊗[F] E},
      (∀ a, (adMat F (cT (σ : E →+* E) X * J) *ᵥ y) (e a) = 0) →
      ((∀ b : Fin d, r' ≤ b.val → (adMat F (cT (σ : E →+* E) Y * J) *ᵥ y) (e b) = 0) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) →
      (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y - y ∈ colSpan F X I := fun x I y h1 h2 => by
    rw [hι]
    exact sub_mem_span (X := adMat F X) (Y := adMat F Y) (L := adMat F (cT (σ : E →+* E) X * J))
      (K := adMat F (cT (σ : E →+* E) Y * J)) e _ _ r' (hP x) h1 h2
  have spL : ∀ {I : Set (Fin r)}, ∀ y ∈ colSpan F X I, ∀ a, (adMat F (cT (σ : E →+* E) X * J) *ᵥ y) (e a) = 0 :=
    fun y hy a => GlobalTheory.BlockForms.Norm.row_span (fun i _ => by rw [hLX]; rfl) hy
  have spK : ∀ {I : Set (Fin r)}, ∀ y ∈ colSpan F X I, ∀ b, e b ∉ I →
      (adMat F (cT (σ : E →+* E) Y * J) *ᵥ y) (e b) = 0 :=
    fun y hy b hb => GlobalTheory.BlockForms.Norm.row_span (fun i hi => by
      rw [hKX, Matrix.one_apply_ne]; rintro rfl; exact hb hi) hy
  have pres : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) {I : Set (Fin r)},
      ((∀ b : Fin d, r' ≤ b.val → e b ∉ I) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) →
      ∀ y ∈ colSpan F X I, (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y ∈ colSpan F X I := fun x I hI y hy => by
    have := add_mem (core x (spL y hy) (hI.imp (fun h b hb => spK y hy b (h b hb)) id)) hy
    rwa [sub_add_cancel] at this
  have u0 : GlobalTheory.CuspRep.unip (0 : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) = 1 := by
    refine Units.ext ?_
    change (1 + GlobalTheory.CuspRep.nilM 0 : Matrix (Fin d) (Fin d) _) = 1
    rw [show GlobalTheory.CuspRep.nilM (0 : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) = 0 from
      Matrix.ext fun i j => by simp [GlobalTheory.CuspRep.nilM], add_zero]
  have hinv : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) y,
      (matHom _ σ J (ι (GlobalTheory.CuspRep.unip (-x)))).1 *ᵥ (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y = y := fun x y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, ← map_mul ι, ← GlobalTheory.CuspRep.unip_add, neg_add_cancel, u0, map_one,
      map_one, Units.val_one, one_mulVec]
  have hiff : ∀ (x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) {I : Set (Fin r)},
      ((∀ b : Fin d, r' ≤ b.val → e b ∉ I) ∨ ∀ a : Fin d, a.val < r' → e a ∈ I) →
      ∀ y, y ∈ colSpan F X I ↔ (matHom _ σ J (ι (GlobalTheory.CuspRep.unip x))).1 *ᵥ y ∈ colSpan F X I :=
    fun x I hI y => ⟨pres x hI y, fun hy => by have := pres (-x) hI _ hy; rwa [hinv x y] at this⟩
  have cJ : ∀ j : Fin r, k < j → ∀ a : Fin d, a.val < r' → e a ∈ {i | ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j} :=
    fun j hj a ha => ⟨k, Finset.mem_insert_self _ _, by change l + a.val ≤ k.val; omega, hj⟩
  have cN : ∀ j : Fin r, ¬ k < j → ∀ b : Fin d, r' ≤ b.val → e b ∉ {i | ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j} := by
    rintro j hj b hb ⟨k', hk', h1, h2⟩
    have h1' : l + b.val ≤ k'.val := h1
    have h2' : k'.val < j.val := h2
    rcases Finset.mem_insert.1 hk' with hk'' | hk''
    · rw [hk''] at h1'; omega
    · have h3 : ¬ k'.val + 1 < l + d := fun h' => hS k' (by omega) h' hk''
      exact hj (Fin.lt_def.2 (by omega))
  have cA : ∀ a : Fin d, e a ∈ {i | ∃ k' ∈ insert k S, i ≤ k'} :=
    fun a => ⟨k0, Finset.mem_insert_of_mem hk0S, by change l + a.val ≤ k0.val; omega⟩
  refine ⟨Subgroup.mem_iInf.2 fun j => ?_, hiff x (Or.inr fun a _ => cA a), fun y hy => ?_⟩
  · by_cases hj : k < j
    · exact ⟨hiff x (Or.inr (cJ j hj)), fun y hy => core x (spL y hy) (Or.inr (cJ j hj))⟩
    · refine ⟨hiff x (Or.inl (cN j hj)), fun y hy => core x (spL y hy) (Or.inl fun b hb => spK y hy b ?_)⟩
      intro hb'
      have hjv : j.val = l + b.val := by rw [← Set.mem_singleton_iff.1 hb']
      exact hj (Fin.lt_def.2 (by omega))
  · refine core x (fun a => ?_) (Or.inr fun a _ => cA a)
    simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hy (e a) (cA a)

end GlobalTheory.BlockForms.CuspUnip

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∀ x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E, ι (GlobalTheory.CuspRep.unip x) ∈ GlobalTheory.StdPar.unip σ J Xf (insert k S) := by
  atlas_forward_decl GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockRat

theorem blockEmb_ratGL_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ l d h ι hι γ
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)
  refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
    GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
  rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
  simp [Matrix.map_add, Matrix.map_sub, Matrix.map_mul, Matrix.map_one]

end GlobalTheory.CuspBlockRat

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  atlas_forward_decl GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.BlockForms

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem isBlockEmb_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  intro F E _ _ _ _ _ _ σ hσ n J _ r Xf Yf _ l d h ι hι
  obtain ⟨Φ, j, _, hΦs, -, -, hform⟩ := hι
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsig : Continuous (sigR (AF F) σ) := by
    have hc := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine hc.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => g.1.map Φ.symm :=
    Units.continuous_val.matrix_map hΦs
  have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g⁻¹).1.map Φ.symm :=
    Units.continuous_coe_inv.matrix_map hΦs
  have h3 : Continuous fun g : GlobalTheory.CuspRep.GA E d => Matrix.transpose (((g⁻¹).1.map Φ.symm).map (sigR (AF F) σ)) :=
    (h2.matrix_map hsig).matrix_transpose
  have hM : Continuous fun g : GlobalTheory.CuspRep.GA E d => (matHom _ σ J (ι g)).1 := by
    refine Continuous.congr ?_ fun g => (hform g).symm
    exact (continuous_const.add ((continuous_const.matrix_mul (h1.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)
  have hMi : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom _ σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
    refine (hM.comp continuous_inv).congr fun g => ?_
    simp only [Function.comp_apply, map_inv]
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hM, hMi⟩)

end GlobalTheory.BlockForms
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  atlas_forward_decl GlobalTheory.BlockForms.isBlockEmb_continuous
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Proj

open GlobalTheory.StdPar

section Abstract

variable {A : Type} [CommRing A] {n r : ℕ} {X : Matrix (Fin n) (Fin r) A} {K : Matrix (Fin r) (Fin n) A}

theorem mulVec_left_inv (hKX : K * X = 1) {I : Set (Fin r)} {y : Fin n → A}
    (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : X *ᵥ (K *ᵥ y) = y := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.eqLocus (X * K).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, -, rfl⟩
    change (X * K * X).col i = _
    rw [Matrix.mul_assoc, hKX, Matrix.mul_one]
    rfl
  rw [mulVec_mulVec]
  exact this hy

theorem mulVec_mem_span {I : Set (Fin r)} {a : Fin r → A} (ha : ∀ i, i ∉ I → a i = 0) :
    X *ᵥ a ∈ Submodule.span A ((fun i => Xᵀ i) '' I) := by
  rw [mulVec_eq_sum]
  refine sum_mem fun i _ => ?_
  rw [op_smul_eq_smul]
  by_cases hi : i ∈ I
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [ha i hi, zero_smul]
    exact zero_mem _

theorem coef_mul (hKX : K * X = 1) (M N : Matrix (Fin n) (Fin n) A) (hN : (N - 1) * X = X * (K * ((N - 1) * X))) :
    K * ((M * N - 1) * X) = K * ((M - 1) * X) + K * ((N - 1) * X) + K * ((M - 1) * X) * (K * ((N - 1) * X)) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc K, Matrix.mul_assoc (M - 1) X, ← hN,
    Matrix.mul_assoc (M - 1)]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
  {K : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}

omit [NumberField E] in

theorem col_mem {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) (j : Fin r) :
    (((matHom _ σ J g).1 - 1) * adMat F X).col j ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := by
  have := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  rw [Matrix.sub_mul, Matrix.one_mul]
  exact this

omit [NumberField E] in

theorem coef_eq_zero (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {i j : Fin r}
    (hi : ¬ ∃ k ∈ T, i ≤ k ∧ k < j) : (K * (((matHom _ σ J g).1 - 1) * adMat F X) : Matrix (Fin r) (Fin r) _) i j = 0 :=
  Norm.row_span (Z := K) (a := i) (fun m hm => by
    rw [hKX, Matrix.one_apply_ne]
    rintro rfl
    exact hi hm) (col_mem hg j)

omit [NumberField E] in

theorem eq_mul_coef (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) :
    ((matHom _ σ J g).1 - 1) * adMat F X = adMat F X * (K * (((matHom _ σ J g).1 - 1) * adMat F X)) :=
  Matrix.ext_col fun j => (mulVec_left_inv hKX (col_mem hg j)).symm

theorem exists_blockProj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, hΦc, _, hj, hΦ, hι⟩ hS ⟨k₀, hk₀, hk₀'⟩ hl r' hr0 hrd k hk
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKY : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [hm, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show jj (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  let c : GAd σ J → Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun g =>
    adMat F (cT (σ : E →+* E) Y * J) * (((matHom _ σ J g).1 - 1) * adMat F X)
  have hc : Continuous c := continuous_const.matrix_mul ((continuous_mat.sub continuous_const).matrix_mul continuous_const)
  refine ⟨fun a p => Φ (c a (e p.1.1) (e p.1.2)), ?_, fun a b => ?_, fun a x hx => ?_, fun a => ⟨fun h0 => ?_, fun ha => ?_⟩,
    fun a ha => ?_⟩
  · exact continuous_pi fun p => hΦc.comp ((hc.comp continuous_subtype_val).matrix_elem _ _)
  · funext p
    have h1 : c (a * b : unip σ J X (insert k S)) = c a + c b + c a * c b := by
      simp only [c]
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
      exact coef_mul hKX _ _ (eq_mul_coef hKX b.2)
    have h2 : (c a * c b) (e p.1.1) (e p.1.2) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hp2 := p.1.2.2
      by_cases hmk : m ≤ k
      · rw [show c a (e p.1.1) m = 0 from coef_eq_zero hKX a.2 ?_, zero_mul]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : l + p.1.1.val ≤ k'.val := h3
        have h4' : k'.val < m.val := h4
        have h5 : m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
      · rw [show c b m (e p.1.2) = 0 from coef_eq_zero hKX b.2 ?_, mul_zero]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : m.val ≤ k'.val := h3
        have h4' : k'.val < l + p.1.2.val := h4
        have h5 : ¬ m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
    change Φ (c (a * b : unip σ J X (insert k S)) _ _) = Φ _ + Φ _
    rw [h1, Matrix.add_apply, h2, add_zero, Matrix.add_apply, map_add]
  · funext p
    have b1 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h X) = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hKX (e i)) (e j)).trans (by simp [Matrix.one_apply, e, Fin.ext_iff])
    have b2 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h Y) = 0 := Matrix.ext fun i j =>
      congrFun (congrFun hKY (e i)) (e j)
    have h1 : c a (e p.1.1) (e p.1.2) = (adMat F (cT (σ : E →+* E) (blkCols h Y) * J) *
        (((matHom _ σ J (a : GAd σ J)).1 - 1) * adMat F (blkCols h X)) : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 := rfl
    have hne : p.1.1 ≠ p.1.2 := fun h' => by have := p.2; rw [h'] at this; omega
    change Φ (c a _ _) = _
    rw [h1, hx, hι, add_assoc, add_sub_cancel_left, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc, b1,
      Matrix.mul_one, ← Matrix.mul_assoc, b1, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F _),
      b2, Matrix.zero_mul, add_zero, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.map_apply,
      RingEquiv.apply_symm_apply]
    change (1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dif_pos p.2]
  · have ha := a.2
    have hset : {i | ∃ k' ∈ insert k S, i ≤ k'} = {i | ∃ k' ∈ S, i ≤ k'} := Set.ext fun i =>
      ⟨fun ⟨k', hk', h1⟩ => by
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · exact ⟨k₀, hk₀, h1.trans (show k'.val ≤ k₀.val by omega)⟩
        · exact ⟨k', hk', h1⟩,
      fun ⟨k', hk', h1⟩ => ⟨k', Finset.mem_insert_of_mem hk', h1⟩⟩
    refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan ha ?_, fun y hy => ?_⟩, hset ▸ ha.2⟩
    · rintro i ⟨k', hk', hik, hkj⟩ m hm
      exact ⟨k', hk', hm.le.trans hik, hkj⟩
    · unfold colSpan at hy
      rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
      obtain ⟨t, rfl⟩ := hy
      rw [mulVec_smul, ← smul_sub]
      refine Submodule.smul_mem _ t ?_
      have h1 : (matHom _ σ J (a : GAd σ J)).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j = adMat F X *ᵥ (c a).col j := by
        have := congrArg (fun Z => Matrix.col Z j) (eq_mul_coef hKX ha)
        rw [Matrix.sub_mul, Matrix.one_mul] at this
        refine Eq.trans ?_ (this.trans ?_)
        · rfl
        · simp only [c]
          rw [Matrix.sub_mul, Matrix.one_mul]
          rfl
      rw [h1]
      refine mulVec_mem_span fun i hi => ?_
      by_cases hi' : ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j
      · obtain ⟨k', hk', h2, h3⟩ := hi'
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · have h2' : i.val ≤ k'.val := h2
          have h3' : k'.val < j.val := h3
          have h4 : j.val < l + d := by
            by_contra h4
            exact hi ⟨k₀, hk₀, show i.val ≤ k₀.val by omega, show k₀.val < j.val by omega⟩
          have h5 : l ≤ i.val := by
            by_contra h5
            rcases hl with hl | ⟨p, hp, hp'⟩
            · omega
            · exact hi ⟨p, hp, show i.val ≤ p.val by omega, show p.val < j.val by omega⟩
          have h6 := congrFun h0 ⟨(⟨i.val - l, by omega⟩, ⟨j.val - l, by omega⟩), by constructor <;> dsimp only <;> omega⟩
          have h7 : e ⟨i.val - l, by omega⟩ = i := Fin.ext (show l + (i.val - l) = i.val by omega)
          have h8 : e ⟨j.val - l, by omega⟩ = j := Fin.ext (show l + (j.val - l) = j.val by omega)
          change Φ (c a (e ⟨i.val - l, _⟩) (e ⟨j.val - l, _⟩)) = 0 at h6
          rw [h7, h8] at h6
          exact (map_eq_zero_iff Φ Φ.injective).1 h6
        · exact absurd ⟨k', hk', h2, h3⟩ hi
      · exact coef_eq_zero hKX ha hi'
  · funext p
    change Φ (c a _ _) = 0
    rw [show c a (e p.1.1) (e p.1.2) = 0 from coef_eq_zero hKX ha ?_, map_zero]
    rintro ⟨k', hk', h3, h4⟩
    have h3' : l + p.1.1.val ≤ k'.val := h3
    have h4' : k'.val < l + p.1.2.val := h4
    have hp2 := p.1.2.2
    exact hS k' (by omega) (by omega) hk'
  · obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
    have h1 : (matHom _ σ J (a : GAd σ J)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    refine ⟨fun p => (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X) : Matrix (Fin r) (Fin r) E) (e p.1.1) (e p.1.2), funext fun p => ?_⟩
    have h2 : c a = adMat F (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X)) := by
      simp only [c]
      rw [h1, ← hm (cT (σ : E →+* E) Y * J), ← hm (γ.1 - 1)]
      congr 2
      rw [adMat, adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    change _ = Φ (c a _ _)
    rw [h2]
    exact (hΦE _).symm

end GlobalTheory.BlockForms.Proj

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockProjection_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  atlas_forward_decl GlobalTheory.BlockForms.Proj.exists_blockProj
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory

namespace GlobalTheory.BlockForms.CuspConst

theorem continuous_unip (E : Type) [Field E] [NumberField E] (d r' : ℕ) :
    Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => GlobalTheory.CuspRep.unip x := by
  have hn : Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => (GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [GlobalTheory.CuspRep.nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

open GlobalTheory.Cusp GlobalTheory.AutomorphicL2Unitary in

theorem isCuspidal_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        GlobalTheory.CuspRep.IsCuspidal (fun x => ψ (ι x * g₀)) := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW K _ S l d h ι hι _ hS hk hl ψ hψ g₀ _
  intro r' hr0 hr1 _ _ μ 𝓕 hμ h𝓕 g
  let k : Fin r := ⟨l + r' - 1, by omega⟩
  have hkv : k.val + 1 = l + r' := by simp only [k]; omega
  have hkS : k ∉ S := hS k (by simp only [k]; omega) (by simp only [k]; omega)
  have hSS : S ⊂ insert k S := Finset.ssubset_insert hkS
  set U := GlobalTheory.StdPar.unip σ J X (insert k S) with hU
  set U₀ := GlobalTheory.StdPar.unip σ J X S with hU₀
  have hle : U₀ ≤ U := GlobalTheory.T.standardParabolicUnipotent_mono F E σ hσ n J hJ r X Y hW _ S (Finset.subset_insert _ _)
  haveI : LocallyCompactSpace U₀ := (GlobalTheory.StdPar.isClosed_unip S hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace U := (GlobalTheory.StdPar.isClosed_unip _ hσ hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have cS := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW S
  have cS' := GlobalTheory.T.cocompact_standardParabolicUnipotentRadical_wittFrame F E σ hσ n J hJ r X Y hW (insert k S)
  have esub : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → (ratPts σ J ⊓ U).subgroupOf N = (ratPts σ J).subgroupOf N := by
    intro N hN
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, hN x.2⟩⟩
  have cinf : ∀ {N : Subgroup (GAd σ J)}, N ≤ U → Cocompact (ratPts σ J) N → Cocompact (ratPts σ J ⊓ U) N := by
    intro N hN hc
    unfold Cocompact
    rw [esub hN]
    exact hc
  have hfΓ : LeftInv (ratPts σ J ⊓ U) ψ := fun γ hγ g => by
    obtain ⟨m, hm, hmL, ν, hν, e⟩ := GlobalTheory.T.rational_unipotentRadical_eq_levi_mul_unipotent F E σ hσ n J hJ r X Y hW S (insert k S) (Finset.subset_insert _ _) γ hγ.1 hγ.2
    rw [e, mul_assoc, hψ.1.leftM m hm hmL, hψ.1.leftN ν hν]
  have hnorm : ∀ p ∈ U, ∀ u ∈ U₀, p * u * p⁻¹ ∈ U₀ := by
    intro p hp u hu
    by_cases hS0 : S = ∅
    · subst hS0
      rw [hU₀, GlobalTheory.StdPar.unip_empty, Subgroup.mem_bot] at hu ⊢
      simp [hu]
    obtain ⟨mS, hmS, hmS'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
      S.max'_mem _, fun k hk => S.le_max' k hk⟩
    have hσσ := sigma_sigma hσ
    have eS := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ hσ n J hJ r X Y hW S mS hmS hmS'
    have hCS : IsIsoCols σ J (GlobalTheory.StdPar.initCols X mS) := isIsoCols_of_isWittFrame hW hσσ hJ mS.2
    rw [hU₀, eS] at hu ⊢
    exact conj_mem_unipFlag hJ hσσ hCS _ (GlobalTheory.ConstTrans.unip_le_parFlag F E σ hσ n J hJ r X Y hW (insert k S) S mS
      (Finset.subset_insert _ _) hmS hmS' hp) hu
  obtain ⟨π, hπc, hπm, hπs, hπk, hπr⟩ := GlobalTheory.T.exists_blockProjection_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv
  have hrat := GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints F E σ hσ n J hJ r X Y hW l d h ι hι
  have hιc := GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries F E σ hσ n J hJ r X Y hW l d h ι hι
  have hsN := GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical F E σ hσ n J hJ r X Y hW S l d h ι hι hS hk hl r' hr0 hr1 k hkv

  have h0 : constTermOn (ratPts σ J ⊓ U) U ψ (ι g * g₀) = 0 := by
    obtain ⟨μN, 𝓕N, h1, h2, h3⟩ := exists_mass_one cS'
    rw [constTermOn_eq_of_measure_eq_one ((esub le_rfl).symm ▸ h2) h3 hfΓ]
    exact (hψ.2 _ hSS μN 𝓕N h1 h2 h3 (ι g * g₀)).symm
  have key := GlobalTheory.T.cocompact_normal_subgroup_descent_invariants (GAd σ J) (ratPts σ J ⊓ U) U U₀ hle hnorm (cinf le_rfl cS') (cinf hle cS)
    (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E) (GlobalTheory.CuspRep.ratN E d r') (fun x => ι (GlobalTheory.CuspRep.unip x)) π
    (hιc.comp (continuous_unip E d r')) (fun v w => by rw [GlobalTheory.CuspRep.unip_add, map_mul]) hsN hπc hπm hπs hπk
    (fun v hv => by
      obtain ⟨x, rfl⟩ := hv
      refine ⟨?_, hsN _⟩
      have := GlobalTheory.CuspRep.unip_algebraMap (a := d) (r := r') x
      exact this ▸ hrat _)
    (fun a ha => hπr a ha.1) ψ hfΓ hψ.1.cont (fun m hm g => hψ.1.leftN m hm g) μ 𝓕 hμ h𝓕 (ι g * g₀)
  rw [h0, smul_zero] at key
  simpa only [map_mul, mul_assoc] using key

end GlobalTheory.BlockForms.CuspConst

end
end
