import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibrationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff

section
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Orb

theorem isMulRightInvariant_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun x : G => x * g) = fun x => g * x := funext fun x => IsMulCommutative.is_comm.comm x g
    rw [this]
    exact map_mul_left_eq_self μ g⟩

section Weight

variable {H : Type} [Group H]

theorem exists_nt_mul {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (p q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((p.1 : H) * p.2) * ((q.1 : H) * q.2) :=
  ⟨(p.1 * ⟨(p.2 : H) * q.1 * (p.2 : H)⁻¹, hnorm _ p.2.2 _ q.1.2⟩, p.2 * q.2), by simp [mul_assoc]⟩

theorem exists_nt_inv {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((q.1 : H) * q.2)⁻¹ :=
  ⟨(⟨(q.2 : H)⁻¹ * (q.1 : H)⁻¹ * (q.2 : H)⁻¹⁻¹, hnorm _ (inv_mem q.2.2) _ (inv_mem q.1.2)⟩, q.2⁻¹), by
    simp only [Subgroup.coe_inv, inv_inv, mul_inv_rev]; group⟩

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_weight_nt (T N : Subgroup H) (hT : IsClosed (T : Set H)) (hN : IsClosed (N : Set H))
    (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hj : Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2))
    (dt : Measure T) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
    (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] :
    ∃ β : H → ℝ≥0∞, Measurable β ∧ (∀ x, β x ≠ ∞) ∧ (∀ n ∈ N, ∀ x, β (n * x) = β x) ∧
      ∀ x, ∫⁻ t : T, β (t * x) ∂dt = 1 := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  set j : N × T → H := fun p => (p.1 : H) * p.2 with hjdef
  have hjc : Continuous j := hj.continuous
  let K := CompactExhaustion.choice H
  let W : ℕ → Set H := fun k => interior (K (k + 1))
  have hWo : ∀ k, IsOpen (W k) := fun k => isOpen_interior
  let U : ℕ → Set H := fun k => {x | ∃ p : N × T, j p * x ∈ W k}
  have hUfwd : ∀ k q x, x ∈ U k → j q * x ∈ U k := by
    rintro k q x ⟨p, hp⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    obtain ⟨s, hs⟩ := exists_nt_mul hnorm p r
    refine ⟨s, ?_⟩
    have e : j s * (j q * x) = j p * x := by
      rw [show j s = j p * j r from hs, show j r = (j q)⁻¹ from hr]; group
    rw [e]; exact hp
  have hU : ∀ k q x, j q * x ∈ U k ↔ x ∈ U k := by
    refine fun k q x => ⟨fun h => ?_, hUfwd k q x⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    have := hUfwd k r _ h
    rwa [show j r = (j q)⁻¹ from hr, inv_mul_cancel_left] at this
  have hUo : ∀ k, IsOpen (U k) := fun k => by
    have : U k = ⋃ p : N × T, (fun x => j p * x) ⁻¹' W k := by ext x; simp [U]
    rw [this]
    exact isOpen_iUnion fun p => (hWo k).preimage (continuous_mul_left _)
  have hcov : ∀ x, ∃ k, x ∈ U k := fun x => by
    obtain ⟨k, hk⟩ := K.exists_mem x
    exact ⟨k, (1, 1), by simpa [j] using K.subset_interior_succ k hk⟩
  let P : ℕ → Set H := disjointed U
  have hPm : ∀ k, MeasurableSet (P k) := MeasurableSet.disjointed fun k => (hUo k).measurableSet
  have hP : ∀ k q x, j q * x ∈ P k ↔ x ∈ P k := fun k q x => by
    simp only [P, disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff, hU]
  have hPcov : ∀ x, ∃ k, x ∈ P k := fun x => by
    have : x ∈ ⋃ k, P k := by rw [iUnion_disjointed]; exact mem_iUnion.2 (hcov x)
    exact mem_iUnion.1 this
  have hPd : ∀ k k' x, x ∈ P k → x ∈ P k' → k = k' := fun k k' x h h' => by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed U hne) h h'
  let h : H → ℝ≥0∞ := fun x => ∑' k, (P k).indicator ((W k).indicator 1) x
  have hh : Measurable h := Measurable.ennreal_tsum fun k =>
    (measurable_one.indicator (hWo k).measurableSet).indicator (hPm k)
  have hval : ∀ k x, x ∈ P k → ∀ q, h (j q * x) = (W k).indicator 1 (j q * x) := by
    intro k x hx q
    have hx' := (hP k q x).2 hx
    refine (tsum_eq_single k fun k' hk' => ?_).trans (indicator_of_mem hx' _)
    exact indicator_of_notMem (fun h' => hk' (hPd _ _ _ h' hx')) _
  let g : H → ℝ≥0∞ := fun x => ∫⁻ n : N, h (n * x) ∂dn
  let I : H → ℝ≥0∞ := fun x => ∫⁻ t : T, g (t * x) ∂dt
  have hg : Measurable g := measurable_fiber hh
  have hI : Measurable I := measurable_fiber hg
  have hgN : ∀ n ∈ N, ∀ x, g (n * x) = g x := fun n hn x => by
    simpa [g, mul_assoc] using lintegral_mul_right_eq_self (μ := dn) (fun m : N => h (m * x)) ⟨n, hn⟩
  have hIN : ∀ n ∈ N, ∀ x, I (n * x) = I x := fun n hn x => by
    refine lintegral_congr fun t => ?_
    have e : (t : H) * (n * x) = ((t : H) * n * (t : H)⁻¹) * (t * x) := by group
    rw [e, hgN _ (hnorm _ t.2 _ hn)]
  have hIT : ∀ s ∈ T, ∀ x, I (s * x) = I x := fun s hs x => by
    simpa [I, mul_assoc] using lintegral_mul_right_eq_self (μ := dt) (fun t : T => g (t * x)) ⟨s, hs⟩
  have hIprod : ∀ x, I x = ∫⁻ p, h (j p * x) ∂(dn.prod dt) := fun x => by
    rw [lintegral_prod_symm (fun p => h (j p * x)) (hh.comp (hjc.measurable.mul_const x)).aemeasurable]
    simp [I, g, j, mul_assoc]
  have hcpt : ∀ k x, IsCompact ((fun y => y * x) ⁻¹' K (k + 1)) := fun k x => by
    have := (Homeomorph.mulRight x).isCompact_preimage.2 (K.isCompact (k + 1))
    simpa using this
  have hIpos : ∀ x, I x ≠ 0 ∧ I x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set E := (fun p => j p * x) ⁻¹' W k with hEdef
    have hE : IsOpen E := (hWo k).preimage (hjc.mul continuous_const)
    have e : I x = dn.prod dt E := by
      rw [hIprod, ← lintegral_indicator_one hE.measurableSet]
      exact lintegral_congr fun p => by rw [hval k x hk p]; rfl
    obtain ⟨p, hp⟩ := disjointed_subset U k hk
    refine ⟨e ▸ hE.measure_ne_zero _ ⟨p, hp⟩, e ▸ ?_⟩
    refine (measure_mono (μ := dn.prod dt) (s := E) (t := j ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))) ?_).trans_lt
      (hj.isCompact_preimage (hcpt k x)).measure_lt_top |>.ne
    intro q hq
    exact interior_subset (s := K (k + 1)) hq
  have hgfin : ∀ x, g x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set C : Set N := (↑) ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))
    have hC : IsCompact C := hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hcpt k x)
    refine ne_of_lt (lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := dn)))
    rw [← lintegral_indicator_one hC.measurableSet]
    refine lintegral_mono fun n => ?_
    have e : h ((n : H) * x) = (W k).indicator 1 ((n : H) * x) := by
      simpa [j] using hval k x hk (n, 1)
    rw [e]
    by_cases hn : (n : H) * x ∈ W k
    · rw [indicator_of_mem hn, indicator_of_mem (show n ∈ C from interior_subset (s := K (k + 1)) hn)]; exact le_rfl
    · rw [indicator_of_notMem hn]; exact zero_le
  refine ⟨fun x => g x * (I x)⁻¹, hg.mul hI.inv, fun x => ENNReal.mul_ne_top (hgfin x)
    (ENNReal.inv_ne_top.2 (hIpos x).1), fun n hn x => by simp only [hgN n hn, hIN n hn], fun x => ?_⟩
  have e : ∀ t : T, g (t * x) * (I (t * x))⁻¹ = g (t * x) * (I x)⁻¹ := fun t => by rw [hIT _ t.2]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hIpos x).1)]
  exact ENNReal.mul_inv_cancel (hIpos x).1 (hIpos x).2

end Weight

theorem quotInt_eq_zero_of_integral_coset_eq_zero : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T →
    (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) →
    ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure]
    [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ →
    Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  intro H _ _ _ _ _ _ _ _ T N hT hN hc hnorm hj dh _ dt _ dn _ _ φ hφ hφT hint h0
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_of_isMulCommutative dt
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  obtain ⟨β, hβm, hβf, hβN, hβ1⟩ := exists_weight_nt T N hT hN hnorm hj dt dn
  have hν : quotMeas T dt dh = (dh.withDensity β).map (mk T) :=
    (isQuotMeasure_quotMeas dt dh hT).eq_map hβm hβ1
  have hlt : ∀ᵐ x ∂dh, β x < ∞ := .of_forall fun x => lt_top_iff_ne_top.2 (hβf x)
  have hD : Measurable (descend T φ) := measurable_descend hφT hφ
  have hcomp : descend T φ ∘ mk T = φ := funext hφT.descend_mk
  have hφβ : Integrable φ (dh.withDensity β) := by
    rw [hν] at hint
    have := (integrable_map_measure hD.aestronglyMeasurable measurable_mk.aemeasurable).1 hint
    rwa [hcomp] at this
  have hF : Integrable (fun x => (β x).toReal • φ x) dh :=
    (integrable_withDensity_iff_integrable_smul' hβm hlt).1 hφβ
  have e1 : quotInt T dt dh φ = ∫ x, (β x).toReal • φ x ∂dh := by
    rw [quotInt, hν, integral_map measurable_mk.aemeasurable hD.aestronglyMeasurable,
      ← integral_withDensity_eq_integral_toReal_smul hβm hlt]
    exact integral_congr_ae (.of_forall fun x => hφT.descend_mk x)
  have hW := (weil_integral (dt := dn) hN hF).2
  have e2 : (fun x => ∫ n : N, (β (n * x)).toReal • φ (n * x) ∂dn) = fun _ => (0 : ℂ) := funext fun x => by
    have e : ∀ n : N, (β (n * x)).toReal • φ (n * x) = (β x).toReal • φ (n * x) := fun n => by
      rw [hβN _ n.2 x]
    simp_rw [e]
    rw [integral_smul, h0 x, smul_zero]
  rw [e1, ← hW.2, e2]
  simp [quotInt, descend]

end GlobalTheory.Orb
end
end

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T → (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) → ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ → Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  atlas_forward_decl GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero
end

section
section
open MeasureTheory GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

theorem mul_comm_of_mem {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {a b : GL (Fin r) k} (ha : a ∈ N) (hb : b ∈ N) :
    a * b = b * a := by
  have hX := (hN a).1 ha
  have hY := (hN b).1 hb
  have h0 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  have hXY : (a.1 - 1) * (b.1 - 1) = 0 := by
    rw [← hX, ← hY]
    calc ε * (a.1 - 1) * (1 - ε) * (ε * (b.1 - 1) * (1 - ε))
        = ε * (a.1 - 1) * ((1 - ε) * ε) * (b.1 - 1) * (1 - ε) := by simp only [mul_assoc]
      _ = 0 := by rw [h0]; simp
  have hYX : (b.1 - 1) * (a.1 - 1) = 0 := by
    rw [← hX, ← hY]
    calc ε * (b.1 - 1) * (1 - ε) * (ε * (a.1 - 1) * (1 - ε))
        = ε * (b.1 - 1) * ((1 - ε) * ε) * (a.1 - 1) * (1 - ε) := by simp only [mul_assoc]
      _ = 0 := by rw [h0]; simp
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ← sub_eq_zero]
  have : a.1 * b.1 - b.1 * a.1 = (a.1 - 1) * (b.1 - 1) - (b.1 - 1) * (a.1 - 1) := by noncomm_ring
  rw [this, hXY, hYX, sub_self]

theorem mul_idem_eq {ε M : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) (hM : ε * (M - 1) * (1 - ε) = M - 1) :
    M * ε = ε ∧ (1 - ε) * M = 1 - ε := by
  have h0 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  have h1 : (M - 1) * ε = 0 := by
    rw [← hM, mul_assoc, h0, mul_zero]
  have h2 : (1 - ε) * (M - 1) = 0 := by
    rw [← hM, ← mul_assoc, ← mul_assoc, h0, zero_mul, zero_mul]
  constructor
  · have : M * ε = (M - 1) * ε + ε := by noncomm_ring
    rw [this, h1, zero_add]
  · have : (1 - ε) * M = (1 - ε) * (M - 1) + (1 - ε) := by noncomm_ring
    rw [this, h2, zero_add]

def diagPart (ε A : Matrix (Fin r) (Fin r) k) : Matrix (Fin r) (Fin r) k := ε * A * ε + (1 - ε) * A * (1 - ε)

theorem diagPart_mul {ε M A : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) (hM : ε * (M - 1) * (1 - ε) = M - 1)
    (hA : A * ε = ε * A) : diagPart ε (M * A) = A ∧ diagPart ε (A * M) = A := by
  obtain ⟨h1, h2⟩ := mul_idem_eq hε hM
  have hA' : A * (1 - ε) = (1 - ε) * A := by rw [mul_sub, sub_mul, mul_one, one_mul, hA]
  have hε' : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε, sub_self, sub_zero]
  have h3 : ε * M * ε = ε := by rw [mul_assoc, h1, hε]
  have hAε : ε * A = A * ε := hA.symm
  have hA'' : (1 - ε) * A = A * (1 - ε) := hA'.symm
  constructor
  · have s1 : ε * (M * A) * ε = ε * A := by
      calc ε * (M * A) * ε = ε * M * (A * ε) := by simp only [mul_assoc]
        _ = ε * (M * ε) * A := by rw [hA]; simp only [mul_assoc]
        _ = ε * A := by rw [h1, hε]
    have s2 : (1 - ε) * (M * A) * (1 - ε) = (1 - ε) * A := by
      calc (1 - ε) * (M * A) * (1 - ε) = (1 - ε) * M * (A * (1 - ε)) := by simp only [mul_assoc]
        _ = (1 - ε) * M * (1 - ε) * A := by rw [hA']; simp only [mul_assoc]
        _ = (1 - ε) * A := by rw [h2, hε']
    rw [diagPart, s1, s2]
    noncomm_ring
  · have s1 : ε * (A * M) * ε = A * ε := by
      calc ε * (A * M) * ε = (ε * A) * M * ε := by simp only [mul_assoc]
        _ = A * (ε * M * ε) := by rw [hAε]; simp only [mul_assoc]
        _ = A * ε := by rw [h3]
    have s2 : (1 - ε) * (A * M) * (1 - ε) = A * (1 - ε) := by
      calc (1 - ε) * (A * M) * (1 - ε) = ((1 - ε) * A) * M * (1 - ε) := by simp only [mul_assoc]
        _ = A * ((1 - ε) * M * (1 - ε)) := by rw [hA'']; simp only [mul_assoc]
        _ = A * (1 - ε) := by rw [h2, hε']
    rw [diagPart, s1, s2]
    noncomm_ring

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

theorem continuous_diagPart [TopologicalSpace k] [IsTopologicalRing k] (ε : Matrix (Fin r) (Fin r) k) :
    Continuous (diagPart ε) :=
  (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

theorem isClosedEmbedding_mul [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N T : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) (hT : IsClosed (T : Set (GL (Fin r) k)))
    (hTε : ∀ t ∈ T, t.1 * ε = ε * t.1) :
    Topology.IsClosedEmbedding (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by
  have hdiag : ∀ (n : N) (t : T), diagPart ε ((n : GL (Fin r) k) * t).1 = (t : GL (Fin r) k).1 ∧
      diagPart ε ((n : GL (Fin r) k) * t)⁻¹.1 = (t : GL (Fin r) k)⁻¹.1 := fun n t => by
    constructor
    · rw [Units.val_mul]; exact (diagPart_mul hε ((hN _).1 n.2) (hTε _ t.2)).1
    · rw [mul_inv_rev, Units.val_mul]
      exact (diagPart_mul hε ((hN _).1 (inv_mem n.2)) (hTε _ (inv_mem t.2))).2
  have hD := continuous_diagPart ε
  have hm : Continuous (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by fun_prop
  let F : GL (Fin r) k → GL (Fin r) k × (Matrix (Fin r) (Fin r) k × (Matrix (Fin r) (Fin r) k)ᵐᵒᵖ) :=
    fun g => (g, diagPart ε g.1, MulOpposite.op (diagPart ε g⁻¹.1))
  have hF : Continuous F :=
    continuous_id.prodMk ((hD.comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp (hD.comp Units.continuous_coe_inv)))
  have hFm : F ∘ (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) =
      Prod.map id (Units.embedProduct (Matrix (Fin r) (Fin r) k)) ∘
        (fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) ∘ Prod.map Subtype.val Subtype.val := by
    funext p
    simp only [Function.comp_apply, F, Prod.map_apply, id_eq, Units.embedProduct_apply, (hdiag p.1 p.2).1,
      (hdiag p.1 p.2).2]
    rfl
  have hΦ : Topology.IsInducing (fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) := by
    refine Topology.IsInducing.of_comp (g := fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2⁻¹, q.2))
      (by fun_prop) (by fun_prop) ?_
    have : ((fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2⁻¹, q.2)) ∘
        fun q : GL (Fin r) k × GL (Fin r) k => (q.1 * q.2, q.2)) = id := by
      funext q; simp
    rw [this]; exact Topology.IsInducing.id
  have hind : Topology.IsInducing (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by
    refine Topology.IsInducing.of_comp hm hF ?_
    rw [hFm]
    exact (Topology.IsInducing.id.prodMap Units.isEmbedding_embedProduct.isInducing).comp
      (hΦ.comp (Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal))
  have hinj : Function.Injective (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) := by
    intro p q h
    simp only at h
    have ht : (p.2 : GL (Fin r) k) = q.2 :=
      Units.ext (by rw [← (hdiag p.1 p.2).1, ← (hdiag q.1 q.2).1, h])
    have hn : (p.1 : GL (Fin r) k) = q.1 := by rw [ht] at h; exact mul_right_cancel h
    exact Prod.ext (Subtype.ext hn) (Subtype.ext ht)
  have hrange : Set.range (fun p : N × T => (p.1 : GL (Fin r) k) * p.2) =
      (fun g : GL (Fin r) k => (diagPart ε g.1, MulOpposite.op (diagPart ε g⁻¹.1))) ⁻¹'
          (Units.embedProduct (Matrix (Fin r) (Fin r) k) '' (T : Set (GL (Fin r) k))) ∩
        {g | ε * (g.1 * diagPart ε g⁻¹.1 - 1) * (1 - ε) = g.1 * diagPart ε g⁻¹.1 - 1} := by
    ext g
    constructor
    · rintro ⟨⟨n, t⟩, rfl⟩
      refine ⟨⟨t, t.2, ?_⟩, ?_⟩
      · simp only [Units.embedProduct_apply, (hdiag n t).1, (hdiag n t).2]
      · simp only [Set.mem_setOf_eq, (hdiag n t).2]
        rw [← Units.val_mul, mul_inv_cancel_right]
        exact (hN _).1 n.2
    · rintro ⟨⟨t, ht, he⟩, hg⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq, MulOpposite.op_inj] at he
      simp only [Set.mem_setOf_eq, ← he.2, ← Units.val_mul] at hg
      exact ⟨(⟨g * t⁻¹, (hN _).2 hg⟩, ⟨t, ht⟩), by simp⟩
  refine ⟨⟨hind, hinj⟩, ?_⟩
  rw [hrange]
  refine IsClosed.inter ((Units.isClosedEmbedding_embedProduct.isClosedMap _ hT).preimage ?_) ?_
  · exact (hD.comp Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hD.comp Units.continuous_coe_inv))
  · exact isClosed_eq (by fun_prop) (by fun_prop)

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

theorem mul_mul_eq_zero {ε X Y A : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) (hX : ε * X * (1 - ε) = X)
    (hY : ε * Y * (1 - ε) = Y) (hA : A * ε = ε * A) : X * A * Y = 0 := by
  have h0 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, hε, sub_self]
  rw [← hX, ← hY]
  calc ε * X * (1 - ε) * A * (ε * Y * (1 - ε)) = ε * X * ((1 - ε) * (A * ε)) * Y * (1 - ε) := by
        simp only [mul_assoc]
    _ = 0 := by rw [hA, ← mul_assoc (1 - ε), h0]; simp

theorem conj_mem {ε : Matrix (Fin r) (Fin r) k} {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {s : GL (Fin r) k} (hs : s.1 * ε = ε * s.1)
    {n : GL (Fin r) k} (hn : n ∈ N) : s * n * s⁻¹ ∈ N := by
  rw [hN] at hn ⊢
  have h1 : (s * n * s⁻¹).1 - 1 = s.1 * (n.1 - 1) * s⁻¹.1 := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]
  have h2 : s⁻¹.1 * ε = ε * s⁻¹.1 := (Commute.units_inv_left (u := s) hs).eq
  have h2' : s⁻¹.1 * (1 - ε) = (1 - ε) * s⁻¹.1 := by rw [mul_sub, sub_mul, mul_one, one_mul, h2]
  rw [h1]
  calc ε * (s.1 * (n.1 - 1) * s⁻¹.1) * (1 - ε) = (ε * s.1) * (n.1 - 1) * (s⁻¹.1 * (1 - ε)) := by
        simp only [mul_assoc]
    _ = s.1 * (ε * (n.1 - 1) * (1 - ε)) * s⁻¹.1 := by rw [← hs, h2']; simp only [mul_assoc]
    _ = s.1 * (n.1 - 1) * s⁻¹.1 := by rw [hn]

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

theorem inv_val {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {n : GL (Fin r) k} (hn : n ∈ N) :
    (n⁻¹).1 = 1 - (n.1 - 1) := by
  have hX := (hN n).1 hn
  have h := mul_mul_eq_zero (A := 1) hε hX hX (by rw [one_mul, mul_one])
  refine Units.inv_eq_of_mul_eq_one_right ?_
  calc n.1 * (1 - (n.1 - 1)) = 1 - (n.1 - 1) * 1 * (n.1 - 1) := by noncomm_ring
    _ = 1 := by rw [h, sub_zero]

theorem mul_val {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {a b : GL (Fin r) k} (ha : a ∈ N) (hb : b ∈ N) :
    (a * b).1 - 1 = (a.1 - 1) + (b.1 - 1) := by
  have h := mul_mul_eq_zero (A := 1) hε ((hN a).1 ha) ((hN b).1 hb) (by rw [one_mul, mul_one])
  calc (a * b).1 - 1 = (a.1 - 1) + (b.1 - 1) + (a.1 - 1) * 1 * (b.1 - 1) := by
        rw [Units.val_mul]; noncomm_ring
    _ = _ := by rw [h, add_zero]

theorem twist_val {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) {s : GL (Fin r) k} (hs : s.1 * ε = ε * s.1)
    {n : GL (Fin r) k} (hn : n ∈ N) :
    (s⁻¹ * n⁻¹ * s * n).1 - 1 = (n.1 - 1) - s⁻¹.1 * (n.1 - 1) * s.1 := by
  have hX := (hN n).1 hn
  have h := mul_mul_eq_zero hε hX hX hs
  have hss : s⁻¹.1 * s.1 = 1 := Units.inv_mul s
  rw [Units.val_mul, Units.val_mul, Units.val_mul, inv_val hε hN hn]
  calc s⁻¹.1 * (1 - (n.1 - 1)) * s.1 * n.1 - 1
      = (s⁻¹.1 * s.1 - 1) + (s⁻¹.1 * s.1) * (n.1 - 1) - s⁻¹.1 * (n.1 - 1) * s.1
          - s⁻¹.1 * ((n.1 - 1) * s.1 * (n.1 - 1)) := by noncomm_ring
    _ = _ := by rw [hss, h]; noncomm_ring

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

def radSub (ε : Matrix (Fin r) (Fin r) k) : Submodule k (Matrix (Fin r) (Fin r) k) where
  carrier := {X | ε * X * (1 - ε) = X}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [mul_add, add_mul, hX, hY]
  zero_mem' := by simp
  smul_mem' c X hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [Matrix.mul_smul, Matrix.smul_mul, hX]

theorem exists_twist_eq {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {γ : GL (Fin r) k} (hγ : IsRegSS γ.1)
    (hγε : γ.1 * ε = ε * γ.1) (hcore : ∀ Z, ε * Z * (1 - ε) = Z → Z - γ⁻¹.1 * Z * γ.1 = 0 → Z = 0)
    {Y : Matrix (Fin r) (Fin r) k} (hY : ε * Y * (1 - ε) = Y) :
    ∃ X, ε * X * (1 - ε) = X ∧ X - γ⁻¹.1 * X * γ.1 = Y := by
  have hg' : γ⁻¹.1 * ε = ε * γ⁻¹.1 := (Commute.units_inv_left (u := γ) hγε).eq
  let L : Matrix (Fin r) (Fin r) k →ₗ[k] Matrix (Fin r) (Fin r) k :=
    LinearMap.id - (LinearMap.mulLeft k γ⁻¹.1) ∘ₗ (LinearMap.mulRight k γ.1)
  have hL : ∀ X, L X = X - γ⁻¹.1 * X * γ.1 := fun X => by
    simp [L, mul_assoc]
  have hmap : ∀ X ∈ radSub ε, L X ∈ radSub ε := fun X hX => by
    change ε * X * (1 - ε) = X at hX
    change ε * L X * (1 - ε) = L X
    have h1 : γ.1 * (1 - ε) = (1 - ε) * γ.1 := by rw [mul_sub, sub_mul, mul_one, one_mul, hγε]
    rw [hL, mul_sub ε, sub_mul _ _ (1 - ε), hX]
    congr 1
    calc ε * (γ⁻¹.1 * X * γ.1) * (1 - ε) = (ε * γ⁻¹.1) * X * (γ.1 * (1 - ε)) := by simp only [mul_assoc]
      _ = γ⁻¹.1 * (ε * X * (1 - ε)) * γ.1 := by rw [← hg', h1]; simp only [mul_assoc]
      _ = _ := by rw [hX]
  let L' := L.restrict hmap
  have hinj : Function.Injective L' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h := congrArg Subtype.val hX
    simp only [L', LinearMap.restrict_coe_apply, ZeroMemClass.coe_zero] at h
    rw [hL] at h
    exact Subtype.ext (hcore X.1 X.2 h)
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨Y, hY⟩
  have h := congrArg Subtype.val hX
  simp only [L', LinearMap.restrict_coe_apply] at h
  exact ⟨X.1, X.2, (hL X.1).symm.trans h⟩

end GlobalTheory.RadicalOrb

namespace GlobalTheory.RadicalOrb

variable {k : Type} [Field k] {r : ℕ}

theorem integral_twist [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)]
    {ε : Matrix (Fin r) (Fin r) k} (hε : ε * ε = ε) {N : Subgroup (GL (Fin r) k)}
    (hN : ∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) (f : GL (Fin r) k → ℂ)
    (hf : ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0)
    {γ : GL (Fin r) k} (hγ : IsRegSS γ.1) (hγε : γ.1 * ε = ε * γ.1) (dn : Measure N) [dn.IsHaarMeasure]
    (x : GL (Fin r) k) : ∫ n : N, f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) ∂dn = 0 := by
  haveI : T2Space k := GlobalTheory.LocAtTopology.t2Space_of_nonarchimedeanLocalField k
  haveI : SecondCountableTopology k := GlobalTheory.LocAtTopology.secondCountable_localField k
  have hNc : IsClosed (N : Set (GL (Fin r) k)) := by
    have : (N : Set (GL (Fin r) k)) = {g | ε * (g.1 - 1) * (1 - ε) = g.1 - 1} := Set.ext fun g => hN g
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  have hg' : γ⁻¹.1 * ε = ε * γ⁻¹.1 := (Commute.units_inv_left (u := γ) hγε).eq
  have hmem : ∀ n ∈ N, γ⁻¹ * n⁻¹ * γ * n ∈ N := fun n hn => by
    have := conj_mem hN hg' (inv_mem hn)
    rw [inv_inv] at this
    exact mul_mem this hn
  have hcore : ∀ Z, ε * Z * (1 - ε) = Z → Z - γ⁻¹.1 * Z * γ.1 = 0 → Z = 0 := fun Z hZ h => by
    have h1 : Z = γ⁻¹.1 * Z * γ.1 := sub_eq_zero.1 h
    have h2 : Z * γ.1 = γ.1 * Z := by
      calc Z * γ.1 = (γ.1 * γ⁻¹.1) * Z * γ.1 := by rw [Units.mul_inv, one_mul]
        _ = γ.1 * (γ⁻¹.1 * Z * γ.1) := by simp only [mul_assoc]
        _ = γ.1 * Z := by rw [← h1]
    have h3 : Z * ε = ε * Z := hγ.commute h2 hγε.symm
    rw [← hZ, ← h3, mul_assoc, mul_sub, mul_one, hε, sub_self, mul_zero]
  let ψ : N →* N :=
    { toFun := fun n => ⟨γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n, hmem n n.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        refine Subtype.ext (Units.ext ((sub_left_inj (a := (1 : Matrix (Fin r) (Fin r) k))).1 ?_))
        simp only [Subgroup.coe_mul]
        rw [twist_val hε hN hγε (mul_mem a.2 b.2), mul_val hε hN (hmem _ a.2) (hmem _ b.2),
          twist_val hε hN hγε a.2, twist_val hε hN hγε b.2, mul_val hε hN a.2 b.2]
        noncomm_ring }
  have hψ : ∀ n : N, ((ψ n : N) : GL (Fin r) k) = γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n := fun n => rfl
  have hψc : Continuous ψ := by
    change Continuous fun n : N => (⟨γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n, hmem n n.2⟩ : N)
    exact Continuous.subtype_mk (by fun_prop) _
  have hinj : Function.Injective ψ := by
    intro a b h
    have h1 := congrArg (fun u : N => (u : GL (Fin r) k).1 - 1) h
    simp only [hψ, twist_val hε hN hγε a.2, twist_val hε hN hγε b.2] at h1
    have hZ : ε * (a.1.1 - b.1.1) * (1 - ε) = a.1.1 - b.1.1 := by
      have ha := (hN _).1 a.2
      have hb := (hN _).1 b.2
      calc ε * (a.1.1 - b.1.1) * (1 - ε) = ε * (a.1.1 - 1) * (1 - ε) - ε * (b.1.1 - 1) * (1 - ε) := by
            noncomm_ring
        _ = _ := by rw [ha, hb]; abel
    have := hcore _ hZ (by rw [← sub_eq_zero] at h1; rw [← h1]; noncomm_ring)
    exact Subtype.ext (Units.ext (sub_eq_zero.1 this))
  have hsurj : Function.Surjective ψ := by
    intro m
    obtain ⟨X, hX, hXY⟩ := exists_twist_eq hε hγ hγε hcore ((hN _).1 m.2)
    have hXX := mul_mul_eq_zero (A := 1) hε hX hX (by rw [one_mul, mul_one])
    rw [mul_one] at hXX
    let u : GL (Fin r) k := ⟨1 + X, 1 - X, by noncomm_ring; rw [hXX]; simp, by noncomm_ring; rw [hXX]; simp⟩
    have hu : u ∈ N := (hN u).2 (by simp only [u, add_sub_cancel_left]; exact hX)
    refine ⟨⟨u, hu⟩, Subtype.ext (Units.ext ((sub_left_inj (a := (1 : Matrix (Fin r) (Fin r) k))).1 ?_))⟩
    rw [hψ, twist_val hε hN hγε hu]
    simp only [u, add_sub_cancel_left]
    exact hXY
  have hopen : IsOpenMap ψ := MonoidHom.isOpenMap_of_sigmaCompact ψ hsurj hψc
  let hom := (Equiv.ofBijective ψ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hψc hopen
  let e : N ≃ₜ* N :=
    { toMulEquiv := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
      continuous_toFun := hom.continuous_toFun
      continuous_invFun := hom.continuous_invFun }
  have he : ∀ n : N, ((e n : N) : GL (Fin r) k) = γ⁻¹ * (n : GL (Fin r) k)⁻¹ * γ * n := fun n => rfl
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  haveI : (dn.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map dn e.toMulEquiv e.continuous e.symm.continuous
  calc ∫ n : N, f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) ∂dn
      = ∫ n : N, f (x⁻¹ * γ * ((e n : N) : GL (Fin r) k) * x) ∂dn := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
        simp only [he]
        congr 1
        group
    _ = ∫ u : N, f (x⁻¹ * γ * u * x) ∂(dn.map e) := (hemb.integral_map (fun u : N => f (x⁻¹ * γ * u * x))).symm
    _ = 0 := hf _ _ _

end GlobalTheory.RadicalOrb

open GlobalTheory.RadicalOrb in
theorem GlobalTheory.RadicalOrb.hasQuotInt_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure] (ε : Matrix (Fin r) (Fin r) k) (N : Subgroup (GL (Fin r) k)), ε * ε = ε → (∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) → ∀ f : GL (Fin r) k → ℂ, Continuous f → HasCompactSupport f → (∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0) → ∀ γ : GL (Fin r) k, IsRegSS γ.1 → γ.1 * ε = ε * γ.1 → ∀ b : GL (Fin r) k → ℂ, Continuous b → LeftInv (cent γ) b → LeftInv N b → ∀ (dt : Measure (cent γ)) [dt.IsHaarMeasure], HasQuotInt (cent γ) dt μ (fun x => b x * f (x⁻¹ * γ * x)) 0 := by
  intro k _ _ _ _ r _ _ μ _ ε N hε hN f hf hfc hnv γ hγ hγε b hb hbT hbN dt _
  haveI : T2Space k := GlobalTheory.LocAtTopology.t2Space_of_nonarchimedeanLocalField k
  haveI : SecondCountableTopology k := GlobalTheory.LocAtTopology.secondCountable_localField k
  have hTε : ∀ t ∈ cent γ, t.1 * ε = ε * t.1 := fun t ht =>
    hγ.commute (congrArg Units.val (mem_cent.1 ht)) hγε.symm
  have hTc : IsMulCommutative (cent γ) := isMulCommutative_cent_GL hγ
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent γ => x * g) = (fun x => g * x) := funext fun x => hTc.is_comm.comm x g
    rw [this, map_mul_left_eq_self]⟩
  have hNc : IsClosed (N : Set (GL (Fin r) k)) := by
    have : (N : Set (GL (Fin r) k)) = {g | ε * (g.1 - 1) * (1 - ε) = g.1 - 1} := Set.ext fun g => hN g
    rw [this]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  let dn : Measure N := Measure.haar
  haveI : dn.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : N => x * g) = (fun x => g * x) :=
      funext fun x => Subtype.ext (mul_comm_of_mem hε hN x.2 g.2)
    rw [this, map_mul_left_eq_self]⟩
  have hφi : LeftInv (cent γ) (fun x => b x * f (x⁻¹ * γ * x)) := fun t ht x => by
    simp only [hbT t ht x]
    exact congrArg _ (leftInv_conjFn le_rfl f t ht x)
  have hφc : Continuous (fun x => b x * f (x⁻¹ * γ * x)) := hb.mul (hf.comp (by fun_prop))
  obtain ⟨C, hC, h0⟩ := isProperOrbit_GL hγ _ hfc
  have hint : Integrable (descend (cent γ) (fun x => b x * f (x⁻¹ * γ * x))) (quotMeas (cent γ) dt μ) :=
    integrable_descend (isClosed_cent γ) hφi hφc hC fun x hx =>
      h0 x (subset_tsupport f (right_ne_zero_of_mul hx))
  refine ⟨hint, ?_⟩
  refine GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals (GL (Fin r) k) (cent γ) N (isClosed_cent γ) hNc hTc
    (fun t ht n hn => conj_mem hN (hTε t ht) hn) (isClosedEmbedding_mul hε hN (isClosed_cent γ) hTε) μ dt dn _ hφc.measurable hφi hint
    fun x => ?_
  · have e : ∀ n : N, b ((n : GL (Fin r) k) * x) * f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) =
        b x * f (((n : GL (Fin r) k) * x)⁻¹ * γ * (n * x)) := fun n => by rw [hbN _ n.2 x]
    simp only [e]
    rw [integral_const_mul, integral_twist hε hN f hnv hγ hγε dn x, mul_zero]
end

open MeasureTheory GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_GL_zero_of_radical_integrals : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure] (ε : Matrix (Fin r) (Fin r) k) (N : Subgroup (GL (Fin r) k)), ε * ε = ε → (∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) → ∀ f : GL (Fin r) k → ℂ, Continuous f → HasCompactSupport f → (∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0) → ∀ γ : GL (Fin r) k, IsRegSS γ.1 → γ.1 * ε = ε * γ.1 → ∀ b : GL (Fin r) k → ℂ, Continuous b → LeftInv (cent γ) b → LeftInv N b → ∀ (dt : Measure (cent γ)) [dt.IsHaarMeasure], HasQuotInt (cent γ) dt μ (fun x => b x * f (x⁻¹ * γ * x)) 0 := by
  atlas_forward_decl GlobalTheory.RadicalOrb.hasQuotInt_zero
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (radical)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_function_constant_term_vanish_split_place : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (a : ℕ), 0 < a → a < V.rank → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin V.rank) (ResF v)) W), τ.IsIrreducible → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ (radical (ResF v) V.rank a) → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) [μ.IsHaarMeasure], ∀ φ ∈ CcLoc D.sp.cm.sig V.gram v, ∀ f : GLoc D.sp.cm.sig V.gram v → ℂ, (f = conv μ (s.idem μ τ) φ ∨ f = conv μ φ (s.idem μ τ)) → ∀ g : GL (Fin V.rank) (Fv D.host.F v), ∃ H : Subgroup (GLoc D.sp.cm.sig V.gram v), IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v)) ∧ (∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a) ∧ ∃ ν : Measure H, ν.IsHaarMeasure ∧ ∀ x y, ∫ u : H, f (x * u * y) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | exact GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | (intros; apply GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt <;> assumption)
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Matrix
noncomputable section
namespace GlobalTheory.TwistLocal

theorem conj_cond {R : Type} [CommRing R] {n : ℕ} (A B M S : Matrix (Fin n) (Fin n) R) (hAB : B * A = 1)
    (hBA : A * B = 1) :
    (A * M * B) * (A * S * B - 1) * (1 - A * M * B) = A * S * B - 1 ↔ M * (S - 1) * (1 - M) = S - 1 := by
  have hX : ∀ X : Matrix (Fin n) (Fin n) R, B * (A * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have e1 : A * S * B - 1 = A * (S - 1) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBA]
  have e2 : 1 - A * M * B = A * (1 - M) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBA]
  rw [e1, e2]
  have e3 : A * M * B * (A * (S - 1) * B) * (A * (1 - M) * B) = A * (M * (S - 1) * (1 - M)) * B := by
    simp only [Matrix.mul_assoc, hX]
  rw [e3]
  constructor
  · intro h
    have := congrArg (fun X => B * X * A) h
    simpa only [Matrix.mul_assoc, hX, hAB, Matrix.mul_one] using this
  · intro h; rw [h]

theorem exists_conj_diag_of_idem (k : Type) [Field k] (r : ℕ) (ε : Matrix (Fin r) (Fin r) k) (hε : ε * ε = ε) :
    ∃ g : GL (Fin r) k, ε * (g : Matrix (Fin r) (Fin r) k) =
      (g : Matrix (Fin r) (Fin r) k) * Matrix.diagonal (fun i : Fin r => if i.val < ε.rank then (1 : k) else 0) := by
  classical
  set f := ε.mulVecLin with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.mulVecLin_mul, hε]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  set U := LinearMap.range f
  set K := LinearMap.ker f
  set a := ε.rank with ha
  have haU : Module.finrank k U = a := rfl
  have hsum : a + Module.finrank k K = r := by
    rw [← haU, Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fin_fun]
  have hKr : Module.finrank k K = r - a := by omega
  let bU : Module.Basis (Fin a) k U := Module.finBasisOfFinrankEq k U haU
  let bK : Module.Basis (Fin (r - a)) k K := Module.finBasisOfFinrankEq k K hKr
  let B : Module.Basis (Fin a ⊕ Fin (r - a)) k (Fin r → k) := (bU.prod bK).map (U.prodEquivOfIsCompl K hc)
  let e : Fin a ⊕ Fin (r - a) ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  let b := B.reindex e
  have hbU : ∀ j : Fin r, j.val < a → b j ∈ U := fun j hj => by
    have hj' : e.symm j = Sum.inl ⟨j.val, hj⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]
    rw [show b j = B (e.symm j) from Module.Basis.reindex_apply _ _ _, hj']
    simp [B]
  have hbK : ∀ j : Fin r, ¬ j.val < a → b j ∈ K := fun j hj => by
    have hj' : e.symm j = Sum.inr ⟨j.val - a, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]; omega
    rw [show b j = B (e.symm j) from Module.Basis.reindex_apply _ _ _, hj']
    simp [B]
  have hfix : ∀ u ∈ U, ε *ᵥ u = u := by
    rintro _ ⟨w, rfl⟩
    show ε *ᵥ (ε *ᵥ w) = ε *ᵥ w
    rw [Matrix.mulVec_mulVec, hε]
  let φ : (Fin r → k) ≃ₗ[k] (Fin r → k) := b.equivFun.symm
  let g : GL (Fin r) k :=
    ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hcol : ∀ j, (g : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single j 1 = b j := fun j => by
    change LinearMap.toMatrix' φ.toLinearMap *ᵥ Pi.single j 1 = b j
    rw [LinearMap.toMatrix'_mulVec]
    simp [φ]
  refine ⟨g, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, Matrix.diagonal_mulVec_single]
  by_cases hj : j.val < a
  · simp only [hj, if_true, mul_one]
    rw [hcol, hfix _ (hbU j hj)]
  · simp only [hj, if_false, zero_mul, Pi.single_zero, Matrix.mulVec_zero]
    exact hbK j hj

theorem diag_cond_iff (k : Type) [Field k] (r a : ℕ) (S : Matrix (Fin r) (Fin r) k) :
    Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) * (S - 1) * (1 - Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0)) = S - 1 ↔
      ∀ i j : Fin r, S i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j → i.val < a ∧ a ≤ j.val := by
  have h1P : (1 : Matrix (Fin r) (Fin r) k) - Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) =
      Matrix.diagonal (fun j : Fin r => 1 - if j.val < a then (1 : k) else 0) := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.diagonal, h]
  have hent : ∀ i j, (Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) * (S - 1) * (1 - Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0))) i j =
      (if i.val < a then (1 : k) else 0) * (S - 1) i j * (1 - if j.val < a then (1 : k) else 0) := by
    intro i j; rw [h1P, Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro h i j hne
    have hz : (S - 1) i j ≠ 0 := by rw [Matrix.sub_apply]; exact sub_ne_zero.2 hne
    rw [← h, hent] at hz
    by_cases hi : i.val < a
    · refine ⟨hi, ?_⟩
      by_contra hj
      push_neg at hj
      simp [hj] at hz
    · simp [hi] at hz
  · intro h
    ext i j
    rw [hent]
    by_cases hij : i.val < a ∧ a ≤ j.val
    · simp [hij.1, not_lt.2 hij.2]
    · have : (S - 1) i j = 0 := by
        by_contra hz
        exact hij (h i j fun e => hz (by rw [Matrix.sub_apply, e, sub_self]))
      simp [this]

theorem idem_conj_radical (k : Type) [Field k] (r : ℕ) (ε : Matrix (Fin r) (Fin r) k) (hε : ε * ε = ε) (a : ℕ)
    (ha : ε.rank = a) :
    ∃ g₀ : GL (Fin r) k, ∀ x : GL (Fin r) k,
      (ε * ((x : Matrix (Fin r) (Fin r) k) - 1) * (1 - ε) = (x : Matrix (Fin r) (Fin r) k) - 1 ↔
        g₀⁻¹ * x * g₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical k r a) := by
  obtain ⟨g, hg⟩ := exists_conj_diag_of_idem k r ε hε
  rw [ha] at hg
  refine ⟨g, fun x => ?_⟩
  have hAB : ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (g : Matrix (Fin r) (Fin r) k) = 1 := Units.inv_mul g
  have hBA : (g : Matrix (Fin r) (Fin r) k) * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = 1 := Units.mul_inv g
  have hεeq : ε = (g : Matrix (Fin r) (Fin r) k) * Matrix.diagonal (fun i : Fin r => if i.val < a then (1 : k) else 0) * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
    rw [← hg, Matrix.mul_assoc, hBA, Matrix.mul_one]
  have hx : (x : Matrix (Fin r) (Fin r) k) = (g : Matrix (Fin r) (Fin r) k) *
      ((g⁻¹ * x * g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc, hBA, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hεeq, hx, conj_cond _ _ _ _ hAB hBA, diag_cond_iff]
  rfl

theorem haar_vanish_transfer {G G' : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
    [IsTopologicalGroup G] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G']
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (e : G ≃ₜ* G') (H : Subgroup G)
    (N : Subgroup G') (hN : IsClosed (N : Set G')) (hHN : ∀ x, e x ∈ N ↔ x ∈ H) (f : G → ℂ) (ν : Measure H)
    [ν.IsHaarMeasure] (h0 : ∀ x y : G, ∫ u : H, f (x * u * y) ∂ν = 0) :
    ∀ (ν' : Measure N) [ν'.IsHaarMeasure] (x y : G'), ∫ u : N, f (e.symm (x * u * y)) ∂ν' = 0 := by
  intro ν' _ x y
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set φ := GlobalTheory.Orb.subEquiv e hHN with hφ
  haveI : (ν.map φ).IsHaarMeasure := φ.isHaarMeasure_map ν
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [Measure.isMulLeftInvariant_eq_smul ν' (ν.map φ), integral_smul_nnreal_measure, hme.integral_map]
  have : ∀ u : H, f (e.symm (x * ((φ u : N) : G') * y)) = f (e.symm x * u * e.symm y) := fun u => by
    congr 1
    show e.symm (x * e u * y) = _
    rw [map_mul, map_mul, e.symm_apply_apply]
  simp only [this, h0, smul_zero]

theorem conj_map_facts {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (τ : E →ₐ[F] K)
    {n : ℕ} (β : GL (Fin n) K) (ε g : Matrix (Fin n) (Fin n) E) (hεε : ε * ε = ε) (hgε : g * ε = ε * g)
    (hg : IsRegSS g) :
    (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) = (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) ∧ (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)).rank = ε.rank ∧ IsRegSS (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g.map τ * (β : Matrix (Fin n) (Fin n) K)) ∧ (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) = (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g.map τ * (β : Matrix (Fin n) (Fin n) K)) ∧
    ∀ S : Matrix (Fin n) (Fin n) K, (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K)) * (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * S * (β : Matrix (Fin n) (Fin n) K) - 1) * (1 - (((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ε.map τ * (β : Matrix (Fin n) (Fin n) K))) = ((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * S * (β : Matrix (Fin n) (Fin n) K) - 1 ↔
      ε.map τ * (S - 1) * (1 - ε.map τ) = S - 1 := by
  set A := ((β⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA
  set B := (β : Matrix (Fin n) (Fin n) K) with hB
  have hAB : B * A = 1 := Units.mul_inv β
  have hBA : A * B = 1 := Units.inv_mul β
  have hX : ∀ X : Matrix (Fin n) (Fin n) K, B * (A * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hm : ∀ M N : Matrix (Fin n) (Fin n) E, (M * N).map τ = M.map τ * N.map τ := fun M N =>
    Matrix.map_mul (f := τ.toRingHom)
  refine ⟨?_, ?_, ?_, ?_, fun S => conj_cond A B _ _ hAB hBA⟩
  · simp only [Matrix.mul_assoc, hX]
    simp only [← Matrix.mul_assoc, ← hm, hεε]
  · rw [Matrix.rank_mul_eq_left_of_isUnit_det B _ ((Matrix.isUnit_iff_isUnit_det _).1 β.isUnit),
      Matrix.rank_mul_eq_right_of_isUnit_det A _ ((Matrix.isUnit_iff_isUnit_det _).1 β⁻¹.isUnit)]
    exact GlobalTheory.Core.Rk.rank_map_field τ.toRingHom ε
  · have h1 := Matrix.charpoly_units_conj' β (g.map τ)
    unfold IsRegSS
    rw [hA, hB, Matrix.coe_units_inv, h1]
    exact hg.map τ.toRingHom
  · simp only [Matrix.mul_assoc, hX]
    simp only [← Matrix.mul_assoc, ← hm, hgε]

set_option maxHeartbeats 1600000 in

theorem weighted_orbital_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ v : T.S, (μf v).IsHaarMeasure → ∀ (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), IsRegSS γ.1.1 → ε * ε = ε → γ.1.1 * ε = ε * γ.1.1 → 0 < ε.rank → ε.rank < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank ε.rank) → ∀ b : GLoc D.sp.cm.sig V.gram v → ℂ, Continuous b → LeftInv (cent (proj D.sp.cm.sig V.gram v (rat V γ))) b → (∀ g, ε.map (T.frame v).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1) * (1 - ε.map (T.frame v).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1 → ∀ x, b (g * x) = b x) → ∀ (dt : Measure (cent (proj D.sp.cm.sig V.gram v (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (proj D.sp.cm.sig V.gram v (rat V γ))) dt (μf v) (fun x => b x * ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x)) 0 := by
  intro hT D V T U μf ff hf v hμ γ ε hγ hεε hγε ha0 har hnf b hb hbL hbN dt _
  letI := GlobalTheory.LocalData.complRel v.1
  haveI := GlobalTheory.LocalData.isLocalField v.1
  have he_apply : ∀ g, (((T.frame v).equiv g : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) =
      (((T.frame v).basis⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) *
        ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * (((T.frame v).basis : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := fun g => by
    have : (T.frame v).equiv g = (T.frame v).basis⁻¹ * splitHom D.sp.cm.sig V.gram (T.frame v).emb g * (T.frame v).basis :=
      splitEquivIn_apply (T.frame v).cm (T.frame v).herm (T.frame v).emb (T.frame v).basis g
    rw [this, Units.val_mul, Units.val_mul]
  haveI : SecondCountableTopology (GL (Fin V.rank) (Fv D.host.F v.1)) :=
    (T.frame v).equiv.symm.toHomeomorph.isEmbedding.secondCountableTopology

  obtain ⟨e, he⟩ : ∃ e, (T.frame v).equiv = e := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, (T.frame v).basis = β := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, (T.frame v).emb = τ := ⟨_, rfl⟩
  rw [he, hβ, hτ] at he_apply
  rw [hτ] at hbN
  obtain ⟨hεε', hrank, hreg0, hcε0, hcond⟩ := conj_map_facts τ β ε γ.1.1 hεε hγε hγ
  have hsplit : ((splitHom D.sp.cm.sig V.gram τ (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) = γ.1.1.map τ := by
    rw [proj_ratEmb]; exact splitEquiv_ratLoc (T.frame v).cm (T.frame v).herm τ γ
  have hγval : ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) = ((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * γ.1.1.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) :=
    (he_apply _).trans (congrArg (fun X => ((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * X * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) hsplit)
  have hreg : IsRegSS ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := by rw [hγval]; exact hreg0
  have hcε : ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) = (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) * ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := by
    rw [hγval]; exact hcε0
  obtain ⟨g₀, hg₀⟩ := idem_conj_radical (Fv D.host.F v.1) V.rank _ hεε' ε.rank hrank
  obtain ⟨h, hh, hffv⟩ := hf.2.1 v
  have hφ : conv (μf v) (T.idem μf v) h ∈ CcLoc D.sp.cm.sig V.gram v :=
    conv_mem_SB ((T.frame v).idem_mem _ _) hh
  obtain ⟨H, hHc, hHmem, ν, hν, hν0⟩ := GlobalTheory.T.type_function_constant_term_vanish_split_place hT D V v.1 (T.frame v) ε.rank ha0 har (T.W v) (T.τ v)
    (T.irred v) hnf (μf v) _ hφ (ff v) (Or.inr hffv) g₀
  rw [he] at hHmem
  obtain ⟨N, hNmem⟩ : ∃ N : Subgroup (GL (Fin V.rank) (Fv D.host.F v.1)), ∀ x, x ∈ N ↔ e.symm x ∈ H :=
    ⟨H.comap (e.symm : GL (Fin V.rank) (Fv D.host.F v.1) →* GLoc D.sp.cm.sig V.gram v), fun x => Iff.rfl⟩
  have hN_iff : ∀ x : GL (Fin V.rank) (Fv D.host.F v.1), x ∈ N ↔ (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1))) * ((x : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) - 1) * (1 - (((β⁻¹ : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ε.map τ * (β : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)))) = (x : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) - 1 := fun x => by
    rw [hNmem, hHmem, e.apply_symm_apply]
    exact (hg₀ x).symm
  have hNc : IsClosed (N : Set (GL (Fin V.rank) (Fv D.host.F v.1))) := by
    have : (N : Set (GL (Fin V.rank) (Fv D.host.F v.1))) = e.symm ⁻¹' (H : Set (GLoc D.sp.cm.sig V.gram v)) := Set.ext hNmem
    rw [this]; exact hHc.preimage e.symm.continuous
  have hHN : ∀ x, e x ∈ N ↔ x ∈ H := fun x => by rw [hNmem, e.symm_apply_apply]
  haveI := hν
  have hvan := haar_vanish_transfer e H N hNc hHN (ff v) ν hν0
  have hffmem : ff v ∈ CcLoc D.sp.cm.sig V.gram v := hf.isFinFamily.1 v
  have hfc : Continuous fun x => ff v (e.symm x) := hffmem.1.continuous.comp e.symm.continuous
  have hfcs : HasCompactSupport fun x => ff v (e.symm x) := hffmem.2.comp_homeomorph e.symm.toHomeomorph
  have hcent : ∀ x, e x ∈ cent (e (proj D.sp.cm.sig V.gram v (rat V γ))) ↔ x ∈ cent (proj D.sp.cm.sig V.gram v (rat V γ)) := fun x => by
    rw [mem_cent, mem_cent, ← map_mul, ← map_mul, e.injective.eq_iff]
  have hb'c : Continuous fun x => b (e.symm x) := hb.comp e.symm.continuous
  have hb'L : LeftInv (cent (e (proj D.sp.cm.sig V.gram v (rat V γ)))) fun x => b (e.symm x) := fun t ht g => by
    show b (e.symm (t * g)) = b (e.symm g)
    rw [map_mul]
    exact hbL _ ((hcent _).1 (by rwa [e.apply_symm_apply])) _
  have hb'N : LeftInv N fun x => b (e.symm x) := fun n hn g => by
    show b (e.symm (n * g)) = b (e.symm g)
    rw [map_mul]
    refine hbN _ ?_ _
    have h1 := (hN_iff n).1 hn
    have h2 := he_apply (e.symm n)
    rw [e.apply_symm_apply] at h2
    rw [h2] at h1
    exact (hcond _).1 h1
  haveI : ((μf v).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map (μf v) e
  haveI : (dt.map (subEquiv e hcent)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map dt (subEquiv e hcent)
  have key := GlobalTheory.T.weightedOrbitalIntegral_GL_zero_of_radical_integrals (Fv D.host.F v.1) V.rank ((μf v).map e) _ N hεε' hN_iff (fun x => ff v (e.symm x)) hfc hfcs
    hvan (e (proj D.sp.cm.sig V.gram v (rat V γ))) hreg hcε (fun x => b (e.symm x)) hb'c hb'L hb'N (dt.map (subEquiv e hcent))
  have hcomm : ∀ t t' : cent (proj D.sp.cm.sig V.gram v (rat V γ)), (t : GLoc D.sp.cm.sig V.gram v) * t' = t' * t := by
    intro t t'
    have hc : ∀ t : cent (proj D.sp.cm.sig V.gram v (rat V γ)), ((e t : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) =
        ((e (proj D.sp.cm.sig V.gram v (rat V γ)) : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) * ((e t : GL (Fin V.rank) (Fv D.host.F v.1)) : Matrix (Fin V.rank) (Fin V.rank) (Fv D.host.F v.1)) := fun t => by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mem_cent.1 t.2]
    apply e.injective
    rw [map_mul, map_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact IsRegSS.commute hreg (hc t) (hc t')
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent (proj D.sp.cm.sig V.gram v (rat V γ)) => x * g) = fun x => g * x := funext fun x => Subtype.ext (hcomm x g)
    rw [this]; exact map_mul_left_eq_self dt g⟩
  have hleft : LeftInv (cent (e (proj D.sp.cm.sig V.gram v (rat V γ))))
      (fun x => b (e.symm x) * ff v (e.symm (x⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * x))) := fun t ht g => by
    show b (e.symm (t * g)) * ff v (e.symm ((t * g)⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * (t * g))) =
      b (e.symm g) * ff v (e.symm (g⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * g))
    have h1 : b (e.symm (t * g)) = b (e.symm g) := hb'L t ht g
    have h2 : (t * g)⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * (t * g) = g⁻¹ * (t⁻¹ * (e (proj D.sp.cm.sig V.gram v (rat V γ)) * t)) * g := by group
    rw [h1, h2, ← mem_cent.1 ht, inv_mul_cancel_left]
  have := ((hasQuotInt_map e hcent (isClosed_cent _) dt (μf v) hleft 0).1).1 key
  convert this using 2 with x
  show _ = b (e.symm (e x)) * ff v (e.symm ((e x)⁻¹ * e (proj D.sp.cm.sig V.gram v (rat V γ)) * e x))
  rw [← map_inv, ← map_mul, ← map_mul, e.symm_apply_apply, e.symm_apply_apply]
end GlobalTheory.TwistLocal
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ v : T.S, (μf v).IsHaarMeasure → ∀ (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), IsRegSS γ.1.1 → ε * ε = ε → γ.1.1 * ε = ε * γ.1.1 → 0 < ε.rank → ε.rank < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank ε.rank) → ∀ b : GLoc D.sp.cm.sig V.gram v → ℂ, Continuous b → LeftInv (cent (proj D.sp.cm.sig V.gram v (rat V γ))) b → (∀ g, ε.map (T.frame v).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1) * (1 - ε.map (T.frame v).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v).emb g).1 - 1 → ∀ x, b (g * x) = b x) → ∀ (dt : Measure (cent (proj D.sp.cm.sig V.gram v (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (proj D.sp.cm.sig V.gram v (rat V γ))) dt (μf v) (fun x => b x * ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x)) 0 := by
  atlas_forward_decl GlobalTheory.TwistLocal.weighted_orbital_vanish
end

section
section
noncomputable section

namespace GlobalTheory.SignProj

open Formalism.BasicNotions GlobalTheory.Cusp GlobalTheory.TruncKer GlobalTheory.Chamber
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp IsIsotropic)

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : HSpace E}

def proj (Φ : WittFrame V) (u : SV (wittIndex V)) : V.V →ₗ[E] V.V :=
  ∑ i, if u i = 1 then (V.hT (Φ.f i)).smulRight (Φ.e i)
    else if u i = -1 then (V.hT (Φ.e i)).smulRight (Φ.f i) else 0

def eps (Φ : WittFrame V) (u : SV (wittIndex V)) : Matrix (Fin V.rank) (Fin V.rank) E :=
  LinearMap.toMatrix V.frame V.frame (proj Φ u)

theorem proj_apply (Φ : WittFrame V) (u : SV (wittIndex V)) (y : V.V) :
    proj Φ u y = ∑ i, if u i = 1 then V.hD y (Φ.f i) • Φ.e i
      else if u i = -1 then V.hD y (Φ.e i) • Φ.f i else 0 := by
  simp only [proj, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [HSpace.hD]

variable (Φ : WittFrame V) (u : SV (wittIndex V))

theorem hD_f_e (i j : Fin (wittIndex V)) : V.hD (Φ.f i) (Φ.e j) = if i = j then 1 else 0 := by
  have h := V.herm.eq (Φ.f i) (Φ.e j)
  simp only [HSpace.hD] at *
  have e2 := Φ.ef j i
  simp only [HSpace.hD] at e2
  rw [← h, e2]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

theorem hD_sum_left {ι : Type} (s : Finset ι) (c : ι → V.V) (w : V.V) :
    V.hD (∑ i ∈ s, c i) w = ∑ i ∈ s, V.hD (c i) w := by
  simp only [HSpace.hD, map_sum]

theorem hD_smul_left (a : E) (x w : V.V) : V.hD (a • x) w = a * V.hD x w := by
  simp only [HSpace.hD, map_smul, smul_eq_mul]

theorem hD_sub_left (x y w : V.V) : V.hD (x - y) w = V.hD x w - V.hD y w := by
  simp only [HSpace.hD, map_sub]

theorem proj_e {i : Fin (wittIndex V)} (hi : u i = 1) : proj Φ u (Φ.e i) = Φ.e i := by
  rw [proj_apply, Finset.sum_eq_single i]
  · rw [if_pos hi, Φ.ef, if_pos rfl, one_smul]
  · intro j _ hj
    split_ifs
    · rw [Φ.ef, if_neg (Ne.symm hj), zero_smul]
    · rw [Φ.ee, zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ i) h

theorem proj_f {i : Fin (wittIndex V)} (hi : u i = -1) : proj Φ u (Φ.f i) = Φ.f i := by
  rw [proj_apply, Finset.sum_eq_single i]
  · rw [if_neg (by rw [hi]; decide), if_pos hi, hD_f_e, if_pos rfl, one_smul]
  · intro j _ hj
    split_ifs
    · rw [Φ.ff, zero_smul]
    · rw [hD_f_e, if_neg (Ne.symm hj), zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ i) h

theorem proj_f_eq_zero {i : Fin (wittIndex V)} (hi : u i = 1) : proj Φ u (Φ.f i) = 0 := by
  rw [proj_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h1 h2
  · rw [Φ.ff, zero_smul]
  · have : i ≠ j := fun e => by subst e; rw [hi] at h2; exact absurd h2 (by decide)
    rw [hD_f_e, if_neg this, zero_smul]
  · rfl

theorem proj_e_eq_zero {i : Fin (wittIndex V)} (hi : u i = -1) : proj Φ u (Φ.e i) = 0 := by
  rw [proj_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h1 h2
  · have : i ≠ j := fun e => by subst e; rw [hi] at h1; exact absurd h1 (by decide)
    rw [Φ.ef, if_neg this, zero_smul]
  · rw [Φ.ee, zero_smul]
  · rfl

theorem e_ne_zero (i : Fin (wittIndex V)) : Φ.e i ≠ 0 := fun h => by
  have := Φ.ef i i
  rw [h, if_pos rfl] at this
  simp [HSpace.hD] at this

theorem f_ne_zero (i : Fin (wittIndex V)) : Φ.f i ≠ 0 := fun h => by
  have := Φ.ef i i
  rw [h, if_pos rfl] at this
  simp [HSpace.hD] at this

theorem e_mem_sub {i : Fin (wittIndex V)} (hi : u i = 1) : Φ.e i ∈ Φ.sub u :=
  Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩)

theorem f_mem_sub {i : Fin (wittIndex V)} (hi : u i = -1) : Φ.f i ∈ Φ.sub u :=
  Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩)

theorem proj_mem (y : V.V) : proj Φ u y ∈ Φ.sub u := by
  rw [proj_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · exact Submodule.smul_mem _ _ (e_mem_sub Φ u h1)
  · exact Submodule.smul_mem _ _ (f_mem_sub Φ u h2)
  · exact zero_mem _

theorem proj_self {x : V.V} (hx : x ∈ Φ.sub u) : proj Φ u x = x := by
  have : Φ.sub u ≤ LinearMap.eqLocus (proj Φ u) LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact proj_e Φ u hi
    · exact proj_f Φ u hi
  exact this hx

theorem proj_proj (y : V.V) : proj Φ u (proj Φ u y) = proj Φ u y := proj_self Φ u (proj_mem Φ u y)

theorem hD_proj_f {j : Fin (wittIndex V)} (hj : u j = 1) (y : V.V) :
    V.hD (proj Φ u y) (Φ.f j) = V.hD y (Φ.f j) := by
  rw [proj_apply, hD_sum_left, Finset.sum_eq_single j]
  · rw [if_pos hj, hD_smul_left, Φ.ef, if_pos rfl, mul_one]
  · intro i _ hij
    split_ifs
    · rw [hD_smul_left, Φ.ef, if_neg hij, mul_zero]
    · rw [hD_smul_left, Φ.ff, mul_zero]
    · simp [HSpace.hD]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem hD_proj_e {j : Fin (wittIndex V)} (hj : u j = -1) (y : V.V) :
    V.hD (proj Φ u y) (Φ.e j) = V.hD y (Φ.e j) := by
  rw [proj_apply, hD_sum_left, Finset.sum_eq_single j]
  · rw [if_neg (by rw [hj]; decide), if_pos hj, hD_smul_left, hD_f_e, if_pos rfl, mul_one]
  · intro i _ hij
    split_ifs
    · rw [hD_smul_left, Φ.ee, mul_zero]
    · rw [hD_smul_left, hD_f_e, if_neg hij, mul_zero]
    · simp [HSpace.hD]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem neg_eq_one_iff (s : SignType) : -s = 1 ↔ s = -1 := by decide +revert
theorem neg_eq_neg_one_iff (s : SignType) : -s = -1 ↔ s = 1 := by decide +revert

theorem sub_proj_mem_perp (y : V.V) : y - proj Φ u y ∈ perp V (Φ.sub (-u)) := by
  have : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip (y - proj Φ u y)) := by
    refine Submodule.span_le.2 ?_
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · have hi' : u i = -1 := (neg_eq_one_iff _).1 hi
      show V.hD (y - proj Φ u y) (Φ.e i) = 0
      rw [hD_sub_left, hD_proj_e Φ u hi', sub_self]
    · have hi' : u i = 1 := (neg_eq_neg_one_iff _).1 hi
      show V.hD (y - proj Φ u y) (Φ.f i) = 0
      rw [hD_sub_left, hD_proj_f Φ u hi', sub_self]
  exact GlobalTheory.Cusp.mem_perp.2 fun x hx => this hx

theorem eq_zero_of_mem {x : V.V} (h1 : x ∈ Φ.sub u) (h2 : x ∈ perp V (Φ.sub (-u))) : x = 0 := by
  rw [← proj_self Φ u h1, proj_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with a b
  · rw [GlobalTheory.Cusp.mem_perp.1 h2 _ (f_mem_sub Φ (-u) (by simp [a])), zero_smul]
  · rw [GlobalTheory.Cusp.mem_perp.1 h2 _ (e_mem_sub Φ (-u) (by simp [b])), zero_smul]
  · rfl

theorem exists_ne (hu : u ≠ 0) : ∃ i, u i = 1 ∨ u i = -1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
  have key : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  exact ⟨i, key _ hi⟩

theorem sub_ne_bot (hu : u ≠ 0) : Φ.sub u ≠ ⊥ := by
  obtain ⟨i, hi | hi⟩ := exists_ne u hu
  · exact fun h => e_ne_zero Φ i (by simpa [h] using e_mem_sub Φ u hi)
  · exact fun h => f_ne_zero Φ i (by simpa [h] using f_mem_sub Φ u hi)

theorem sub_le_perp : Φ.sub u ≤ perp V (Φ.sub u) := by
  have gen : ∀ a ∈ Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1},
      ∀ b ∈ Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1}, V.hD a b = 0 := by
    rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) _ (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Φ.ee i j
    · have : i ≠ j := fun e => by
        subst e; exact absurd ((show u i = 1 from hi).symm.trans (show u i = -1 from hj)) (by decide)
      rw [Φ.ef, if_neg this]
    · have : i ≠ j := fun e => by
        subst e; exact absurd ((show u i = -1 from hi).symm.trans (show u i = 1 from hj)) (by decide)
      rw [hD_f_e, if_neg this]
    · exact Φ.ff i j
  refine Submodule.span_le.2 fun a ha => ?_
  have : Φ.sub u ≤ LinearMap.ker (V.hT.flip a) :=
    Submodule.span_le.2 fun b hb => (gen a ha b hb : _)
  exact GlobalTheory.Cusp.mem_perp.2 fun x hx => this hx

theorem isIsotropic_sub (hu : u ≠ 0) : IsIsotropic V (Φ.sub u) := ⟨sub_ne_bot Φ u hu, sub_le_perp Φ u⟩

theorem eps_mul_self : eps Φ u * eps Φ u = eps Φ u := by
  rw [eps, ← LinearMap.toMatrix_comp]
  congr 1
  exact LinearMap.ext fun y => proj_proj Φ u y

theorem rank_eps : (eps Φ u).rank = Module.finrank E (LinearMap.range (proj Φ u)) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ V.frame V.frame, eps, Matrix.toLin_toMatrix]

theorem rank_eps_pos (hu : u ≠ 0) : 0 < (eps Φ u).rank := by
  rw [rank_eps]
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Submodule.finrank_eq_zero] at h
  obtain ⟨i, hi | hi⟩ := exists_ne u hu
  · exact e_ne_zero Φ i (by simpa [proj_e Φ u hi, h] using LinearMap.mem_range_self (proj Φ u) (Φ.e i))
  · exact f_ne_zero Φ i (by simpa [proj_f Φ u hi, h] using LinearMap.mem_range_self (proj Φ u) (Φ.f i))

theorem rank_eps_lt (hu : u ≠ 0) : (eps Φ u).rank < V.rank := by
  rw [rank_eps, ← V.rank_eq]
  refine Submodule.finrank_lt fun h => ?_
  have hinj : Function.Injective (proj Φ u) :=
    LinearMap.injective_iff_surjective.2 (LinearMap.range_eq_top.1 h)
  obtain ⟨i, hi | hi⟩ := exists_ne u hu
  · exact f_ne_zero Φ i (hinj (by rw [proj_f_eq_zero Φ u hi, map_zero]))
  · exact e_ne_zero Φ i (hinj (by rw [proj_e_eq_zero Φ u hi, map_zero]))

end GlobalTheory.SignProj

section Places

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp IsIsotropic extSub coordR act parab unipRad)
open GlobalTheory.SplitFlag
open scoped Matrix TensorProduct

namespace GlobalTheory.SignProj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : HSpace E}

theorem comp_proj (Φ : WittFrame V) (u : SV (wittIndex V)) (T : V.V →ₗ[E] V.V)
    (h1 : ∀ x ∈ Φ.sub u, T x ∈ Φ.sub u) (h2 : ∀ x ∈ perp V (Φ.sub (-u)), T x ∈ perp V (Φ.sub (-u))) :
    T ∘ₗ proj Φ u = proj Φ u ∘ₗ T := by
  refine LinearMap.ext fun y => ?_
  have hz : proj Φ u (T y) - T (proj Φ u y) = 0 := by
    refine eq_zero_of_mem Φ u (sub_mem (proj_mem Φ u _) (h1 _ (proj_mem Φ u y))) ?_
    have e : proj Φ u (T y) - T (proj Φ u y) = T (y - proj Φ u y) - (T y - proj Φ u (T y)) := by
      rw [map_sub]; abel
    rw [e]
    exact sub_mem (h2 _ (sub_proj_mem_perp Φ u y)) (sub_proj_mem_perp Φ u (T y))
  exact (sub_eq_zero.1 hz).symm

end GlobalTheory.SignProj

namespace GlobalTheory.SignProj

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (u : SV (wittIndex V))

theorem comm_of_mem_levi (γ : GF V) (hγ : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u}) :
    γ.1.1 * eps Φ u = eps Φ u * γ.1.1 := by
  simp only [WittFrame.levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hγ
  obtain ⟨hA, hB⟩ := hγ u (Finset.mem_singleton_self u)
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  have h1 : ∀ x ∈ Φ.sub u, ratAct D.sp.cm V γ x ∈ Φ.sub u := (diagH_mem_parab (AF D.host.F)).1 hA
  have h2' : ∀ x ∈ Φ.sub (-u), ratAct D.sp.cm V γ x ∈ Φ.sub (-u) := (diagH_mem_parab (AF D.host.F)).1 hB
  have h2 : ∀ x ∈ perp V (Φ.sub (-u)), ratAct D.sp.cm V γ x ∈ perp V (Φ.sub (-u)) :=
    (diagH_mem_parab D.host.F).1 (parab_le_perp ((diagH_mem_parab D.host.F).2 h2'))
  have hc := comp_proj Φ u _ h1 h2
  have hγm : γ.1.1 = LinearMap.toMatrix V.frame V.frame (ratAct D.sp.cm V γ) :=
    (LinearMap.toMatrix_toLin V.frame V.frame γ.1.1).symm
  rw [hγm, eps, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hc]

theorem splitVec_sub' {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y z : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    splitVec τ (y - z) = splitVec τ y - splitVec τ z := funext fun _ => map_sub _ _ _

theorem epsR_mulVec_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hy : y ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.sub u)) :
    (eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ y = y := by
  have : extSub (F := D.host.F) V (Fv D.host.F v) (Φ.sub u) ≤
      LinearMap.eqLocus ((eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v))).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    change ((eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v))) *ᵥ coordR (F := D.host.F) V (Fv D.host.F v) x =
      coordR (F := D.host.F) V (Fv D.host.F v) x
    rw [map_mulVec_coordR]
    have e : (eps Φ u *ᵥ fun j => V.frame.repr x j) = fun j => V.frame.repr x j := by
      have := LinearMap.toMatrix_mulVec_repr V.frame V.frame (proj Φ u) x
      rw [proj_self Φ u hx] at this
      exact this
    rw [e]
    rfl
  exact this hy

theorem epsR_mulVec_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (a : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    (eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ a ∈ extSub (F := D.host.F) V (Fv D.host.F v) (Φ.sub u) := by
  refine mulVec_mem_extSub V _ _ (fun k => ?_) a
  have : GlobalTheory.AutFunCompare.vecOf V ((eps Φ u)ᵀ k) = proj Φ u (V.frame k) := by
    simp only [GlobalTheory.AutFunCompare.vecOf, eps]
    refine V.frame.repr.injective ?_
    ext i
    simp [LinearMap.toMatrix_apply]
  rw [this]
  exact proj_mem Φ u _

theorem map_epsR {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ((eps Φ u).map (inclR (F := D.host.F) (Fv D.host.F v))).map (splitProj τ) = (eps Φ u).map τ := by
  refine Matrix.ext fun i j => ?_
  exact splitProj_inclR τ (eps Φ u i j)

theorem eps_mulVec_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    {w : Fin V.rank → Fv D.host.F v} (hw : w ∈ wPart τ (Φ.sub u)) : (eps Φ u).map τ *ᵥ w = w := by
  obtain ⟨y, hy, rfl⟩ := hw
  rw [← map_epsR, ← splitVec_mulVec, epsR_mulVec_of_mem Φ u hy]

theorem eps_mulVec_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (w : Fin V.rank → Fv D.host.F v) : (eps Φ u).map τ *ᵥ w ∈ wPart τ (Φ.sub u) := by
  have h := isCMExt_host D
  rw [← splitVec_splitIncl h τ w, ← map_epsR, ← splitVec_mulVec]
  exact splitVec_mem_wPart τ (epsR_mulVec_mem Φ u _)

theorem mem_unipRad (hu : u ≠ 0) (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig V.gram v)
    (H : (eps Φ u).map τ * ((splitHom D.sp.cm.sig V.gram τ g).1 - 1) * (1 - (eps Φ u).map τ) =
      (splitHom D.sp.cm.sig V.gram τ g).1 - 1) :
    g ∈ unipRad D.sp.cm V (Fv D.host.F v) (Φ.sub u) := by
  have h := isCMExt_host D
  have hJ := isHermND_gram V
  set A := (splitHom D.sp.cm.sig V.gram τ g).1 with hA
  set B := (splitHom D.sp.cm.sig V.gram (τ.comp D.sp.cm.sig) g).1 with hB
  set εt := (eps Φ u).map τ
  have T0 : ∀ w, A *ᵥ w - w = εt *ᵥ ((A - 1) *ᵥ ((1 - εt) *ᵥ w)) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, H, Matrix.sub_mulVec, Matrix.one_mulVec]
  have T1 : ∀ w ∈ wPart τ (Φ.sub u), A *ᵥ w = w := fun w hw => by
    have h0 : (1 - εt) *ᵥ w = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, show εt *ᵥ w = w from eps_mulVec_of_mem Φ u τ hw, sub_self]
    have := T0 w
    rw [h0, Matrix.mulVec_zero, Matrix.mulVec_zero] at this
    exact sub_eq_zero.1 this
  have T2 : ∀ w, A *ᵥ w - w ∈ wPart τ (Φ.sub u) := fun w => by
    rw [T0 w]; exact eps_mulVec_mem Φ u τ _
  have T3 : ∀ w' ∈ wPart (τ.comp D.sp.cm.sig) (perp V (Φ.sub u)), B *ᵥ w' = w' := fun w' hw' => by
    have hw'' := (mem_wPart_comp_iff D.sp.cm h hJ τ).1 hw'
    rw [perp_perp] at hw''
    set d := B *ᵥ w' - w'
    have hd : ∀ z, d ⬝ᵥ V.gram.map τ *ᵥ z = 0 := fun z => by
      obtain ⟨z₀, rfl⟩ : ∃ z₀, A *ᵥ z₀ = z := ⟨((splitHom D.sp.cm.sig V.gram τ g)⁻¹).1 *ᵥ z, by
        rw [hA, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
      have e1 : (B *ᵥ w') ⬝ᵥ V.gram.map τ *ᵥ (A *ᵥ z₀) = w' ⬝ᵥ V.gram.map τ *ᵥ z₀ :=
        pairing_splitHom τ g w' z₀
      have e2 : w' ⬝ᵥ V.gram.map τ *ᵥ (A *ᵥ z₀ - z₀) = 0 := hw'' _ (T2 z₀)
      rw [Matrix.mulVec_sub, dotProduct_sub] at e2
      show (B *ᵥ w' - w') ⬝ᵥ V.gram.map τ *ᵥ (A *ᵥ z₀) = 0
      rw [sub_dotProduct, e1]
      linear_combination -e2
    have hv : Matrix.vecMul d (V.gram.map τ) = 0 := funext fun k => by
      have := hd (Pi.single k 1)
      rw [Matrix.dotProduct_mulVec] at this
      simpa using this
    have : d = 0 := by
      have e := congrArg (fun x => Matrix.vecMul x ((splitGram hJ τ)⁻¹).1) hv
      simp only [Matrix.zero_vecMul, Matrix.vecMul_vecMul] at e
      rwa [← splitGram_val hJ τ, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at e
    exact sub_eq_zero.1 this
  have T4 : ∀ w' ∈ wPart (τ.comp D.sp.cm.sig) (Φ.sub u), B *ᵥ w' = w' := fun w' hw' =>
    T3 w' (wPart_mono _ (sub_le_perp Φ u) hw')
  have key : ∀ (τ' : D.host.E →ₐ[D.host.F] Fv D.host.F v) y, splitVec τ' (act D.sp.cm V g y) =
      (splitHom D.sp.cm.sig V.gram τ' g).1 *ᵥ splitVec τ' y := fun τ' y => splitVec_matHom_mulVec τ' g y
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := (mem_extSub_iff_split D.sp.cm h τ).1 hy
    exact splitVec_ext h τ (by rw [key]; exact T1 _ h1) (by rw [key]; exact T4 _ h2)
  · obtain ⟨-, h2⟩ := (mem_extSub_iff_split D.sp.cm h τ).1 hy
    refine (mem_extSub_iff_split D.sp.cm h τ).2 ⟨?_, ?_⟩
    · rw [splitVec_sub', key]; exact T2 _
    · rw [splitVec_sub', key, T3 _ h2, sub_self]; exact zero_mem _

end GlobalTheory.SignProj

theorem GlobalTheory.SignProj.exists_proj_unip : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)), u ≠ 0 →
    ∃ (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u)), ε * ε = ε ∧
      0 < ε.rank ∧ ε.rank < V.rank ∧
      (∀ γ : GF V, rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → γ.1.1 * ε = ε * γ.1.1) ∧
      ∀ v (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GLoc D.sp.cm.sig V.gram v),
        ε.map τ * ((splitHom D.sp.cm.sig V.gram τ g).1 - 1) * (1 - ε.map τ) = (splitHom D.sp.cm.sig V.gram τ g).1 - 1 →
        emb D.sp.cm.sig V.gram v g ∈ NA (IsoFlag.single hW) := by
  intro D V Φ u hu
  refine ⟨GlobalTheory.SignProj.eps Φ u, GlobalTheory.SignProj.isIsotropic_sub Φ u hu, GlobalTheory.SignProj.eps_mul_self Φ u,
    GlobalTheory.SignProj.rank_eps_pos Φ u hu, GlobalTheory.SignProj.rank_eps_lt Φ u hu,
    fun γ hγ => GlobalTheory.SignProj.comm_of_mem_levi Φ u γ hγ, fun v τ g H => ?_⟩
  refine IsoFlag.emb_mem_unip.2 ?_
  rw [IsoFlag.unip_single]
  exact GlobalTheory.SignProj.mem_unipRad Φ u hu v τ g H

end Places
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_idempotent_splitting : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)), u ≠ 0 → ∃ (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u)), ε * ε = ε ∧ 0 < ε.rank ∧ ε.rank < V.rank ∧ (∀ γ : GF V, rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → γ.1.1 * ε = ε * γ.1.1) ∧ ∀ v (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GLoc D.sp.cm.sig V.gram v), ε.map τ * ((splitHom D.sp.cm.sig V.gram τ g).1 - 1) * (1 - ε.map τ) = (splitHom D.sp.cm.sig V.gram τ g).1 - 1 → emb D.sp.cm.sig V.gram v g ∈ NA (IsoFlag.single hW) := by
  atlas_forward_decl GlobalTheory.SignProj.exists_proj_unip
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypesFactor

section Split

variable {ι : Type} [DecidableEq ι] (i : ι) (G : ι → Type) [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)]

def splitEquiv : (∀ j, G j) ≃ₜ* G i × ∀ j : {j // j ≠ i}, G j :=
  { Homeomorph.piSplitAt i G with map_mul' := fun _ _ => rfl }

variable {i G}

theorem splitEquiv_apply (x : ∀ j, G j) : splitEquiv i G x = (x i, fun j : {j // j ≠ i} => x j) := rfl

theorem splitEquiv_symm_self (a : G i) (b : ∀ j : {j // j ≠ i}, G j) : (splitEquiv i G).symm (a, b) i = a :=
  congrArg Prod.fst ((splitEquiv i G).apply_symm_apply (a, b))

theorem splitEquiv_symm_ne (a : G i) (b : ∀ j : {j // j ≠ i}, G j) (j : {j // j ≠ i}) :
    (splitEquiv i G).symm (a, b) j = b j :=
  congrFun (congrArg Prod.snd ((splitEquiv i G).apply_symm_apply (a, b))) j

theorem splitEquiv_symm_one (a : G i) : (splitEquiv i G).symm (a, 1) = Pi.mulSingle i a := by
  apply (splitEquiv i G).injective
  rw [ContinuousMulEquiv.apply_symm_apply, splitEquiv_apply]
  exact Prod.ext (Pi.mulSingle_eq_same i a).symm (funext fun j => (Pi.mulSingle_eq_of_ne j.2 a).symm)

theorem splitEquiv_symm_mem_cent (g : ∀ j, G j) (a : G i) (b : ∀ j : {j // j ≠ i}, G j) :
    (splitEquiv i G).symm (a, b) ∈ cent g ↔ a ∈ cent (g i) ∧ b ∈ cent (fun j : {j // j ≠ i} => g j) := by
  simp only [mem_cent]
  rw [← (splitEquiv i G).injective.eq_iff, map_mul, map_mul, ContinuousMulEquiv.apply_symm_apply, splitEquiv_apply]
  exact Prod.ext_iff

end Split

theorem mem_cent_pi {ι : Type} {G : ι → Type} [∀ j, Group (G j)] {g x : ∀ j, G j} :
    x ∈ cent g ↔ ∀ j, x j ∈ cent (g j) :=
  ⟨fun h j => mem_cent.2 (congrFun (mem_cent.1 h) j), fun h => mem_cent.2 (funext fun j => mem_cent.1 (h j))⟩

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem embAt_mem_cent {S : Finset (HeightOneSpectrum (𝓞 F))} {g : GAd σ J} {x : ∀ v : S, GLoc σ J v}
    (hx : x ∈ cent (projAt σ J S g)) : embAt σ J S x ∈ cent g := by
  have hm := mem_atPts.1 (embAt_mem σ J S x)
  refine mem_cent.2 (GAd_ext σ J (fun w => ?_) fun v => ?_)
  · simp only [map_mul, mem_finPts_iff_forall.1 hm.1 w, one_mul, mul_one]
  · by_cases hv : v ∈ S
    · have h := congrFun (mem_cent.1 hx) ⟨v, hv⟩
      rw [map_mul, map_mul, show proj σ J v (embAt σ J S x) = x ⟨v, hv⟩ from proj_embAt σ J S x ⟨v, hv⟩]
      exact h
    · simp only [map_mul, hm.2 v hv, one_mul, mul_one]

theorem isMulCommutative_cent_projAt (S : Finset (HeightOneSpectrum (𝓞 F))) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (projAt σ J S (ratEmb σ J γ))) :=
  ⟨⟨fun a b => Subtype.ext (funext fun v => by
    have hc := isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)
    exact congrArg Subtype.val (hc.1.1 ⟨a.1 v, mem_cent_pi.1 a.2 v⟩ ⟨b.1 v, mem_cent_pi.1 b.2 v⟩))⟩⟩

theorem leftInv_integrand (S : Finset (HeightOneSpectrum (𝓞 F))) {g : GAd σ J} (ff : ∀ v, GLoc σ J v → ℂ)
    {C : GAd σ J → ℂ} (hCi : LeftInv (cent g) C) :
    LeftInv (cent (projAt σ J S g)) fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v g * x v) := by
  intro t ht x
  simp only [map_mul, Pi.mul_apply]
  rw [hCi _ (embAt_mem_cent σ J ht)]
  congr 1
  refine Finset.prod_congr rfl fun v _ => congrArg (ff v) ?_
  have hc : t v * proj σ J v g = proj σ J v g * t v := mem_cent.1 (mem_cent_pi.1 ht v)
  have e : (t v * x v)⁻¹ * proj σ J v g * (t v * x v) = (x v)⁻¹ * ((t v)⁻¹ * (proj σ J v g * t v)) * x v := by group
  rw [e, ← hc, inv_mul_cancel_left]

theorem integrable_integrand (h : IsCMExt F E σ) (hJ : IsHermND σ J) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (ff : ∀ v, GLoc σ J v → ℂ) (hc : ∀ v : S, Continuous (ff v))
    (hs : ∀ v : S, HasCompactSupport (ff v)) {C : GAd σ J → ℂ} (hC : Continuous C)
    (hCi : LeftInv (cent (ratEmb σ J γ)) C) (dg : Measure (∀ v : S, GLoc σ J v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt σ J S (ratEmb σ J γ)))) [dt.IsHaarMeasure] :
    Integrable (descend (cent (projAt σ J S (ratEmb σ J γ)))
      fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v))
      (quotMeas _ dt dg) := by
  haveI : LocallyCompactSpace (∀ v : S, GLoc σ J v) := Pi.locallyCompactSpace_of_finite
  haveI := isMulRightInvariant_cent (isMulCommutative_cent_projAt σ J S hγ) dt
  have hp : ∀ v : S, IsProperOrbit (cent (proj σ J v (ratEmb σ J γ))) (proj σ J v (ratEmb σ J γ)) :=
    fun v => isProperOrbit_GLoc h hJ (isRegSS_proj_ratEmb hγ v)
  choose K hK hK' using fun v : S => hp v _ (hs v).isCompact
  refine integrable_descend (isClosed_cent _) (leftInv_integrand σ J S ff hCi)
    ((hC.comp (continuous_embAt σ J S)).mul (continuous_finset_prod _ fun v _ =>
      (hc v).comp ((((continuous_apply v).inv).mul continuous_const).mul (continuous_apply v))))
    (isCompact_univ_pi hK) fun x hx => ?_
  have h1 : ∀ v : S, (x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v ∈ tsupport (ff v) := fun v =>
    subset_tsupport _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) v (Finset.mem_univ _))
  choose t ht ht' using fun v => hK' v (x v) (h1 v)
  exact ⟨t, mem_cent_pi.2 ht, fun v _ => ht' v⟩

end Gen

end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
section Gen2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def splitAt (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidableEq S] (v₀ : S) :
    GLoc σ J v₀ × (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) ≃ₜ* ∀ v : S, GLoc σ J v :=
  (splitEquiv v₀ fun v : S => GLoc σ J v).symm

variable {σ J}

theorem splitAt_self {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀)
    (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) : splitAt σ J S v₀ (a, b) v₀ = a :=
  splitEquiv_symm_self (G := fun v : S => GLoc σ J v) a b

theorem splitAt_ne {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀)
    (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) (j : {j : S // j ≠ v₀}) : splitAt σ J S v₀ (a, b) j = b j :=
  splitEquiv_symm_ne (G := fun v : S => GLoc σ J v) a b j

theorem splitAt_one {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀) :
    splitAt σ J S v₀ (a, 1) = Pi.mulSingle v₀ a :=
  splitEquiv_symm_one (G := fun v : S => GLoc σ J v) a

theorem splitAt_mem_cent {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (g : ∀ v : S, GLoc σ J v)
    (a : GLoc σ J v₀) (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) :
    splitAt σ J S v₀ (a, b) ∈ cent g ↔ a ∈ cent (g v₀) ∧ b ∈ cent (fun j : {j : S // j ≠ v₀} => g j) :=
  splitEquiv_symm_mem_cent (G := fun v : S => GLoc σ J v) g a b

end Gen2
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
section Gen3
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem quotInt_const_mul {H : Type} [Group H] [MeasurableSpace H] (T : Subgroup H) (dt : Measure T) (dh : Measure H)
    (c : ℂ) (f : H → ℂ) : quotInt T dt dh (fun x => c * f x) = c * quotInt T dt dh f := by
  simp only [quotInt, GlobalTheory.AutomorphicL2Unitary.descend]
  exact integral_const_mul _ _

theorem hasQuotInt_integrand_zero (h : IsCMExt F E σ) (hJ : IsHermND σ J) (S : Finset (HeightOneSpectrum (𝓞 F)))
    [DecidableEq S] (v₀ : S) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (ff : ∀ v, GLoc σ J v → ℂ)
    (hc : ∀ v : S, Continuous (ff v)) (hs : ∀ v : S, HasCompactSupport (ff v)) (μ : Measure (GLoc σ J v₀))
    [μ.IsHaarMeasure] {C : GAd σ J → ℂ} (hC : Continuous C) (hCi : LeftInv (cent (ratEmb σ J γ)) C)
    (P : GLoc σ J v₀ → Prop) (hCP : ∀ g, P g → ∀ y, C (emb σ J v₀ g * y) = C y)
    (hloc : ∀ bf : GLoc σ J v₀ → ℂ, Continuous bf → LeftInv (cent (proj σ J v₀ (ratEmb σ J γ))) bf →
      (∀ g, P g → ∀ x, bf (g * x) = bf x) → ∀ (ds : Measure (cent (proj σ J v₀ (ratEmb σ J γ)))) [ds.IsHaarMeasure],
      quotInt (cent (proj σ J v₀ (ratEmb σ J γ))) ds μ
        (fun a => bf a * ff v₀ (a⁻¹ * proj σ J v₀ (ratEmb σ J γ) * a)) = 0)
    (dg : Measure (∀ v : S, GLoc σ J v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt σ J S (ratEmb σ J γ)))) [dt.IsHaarMeasure] :
    HasQuotInt (cent (projAt σ J S (ratEmb σ J γ))) dt dg
      (fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v)) 0 := by
  have hint := integrable_integrand σ J h hJ S hγ ff hc hs hC hCi dg dt
  refine ⟨hint, ?_⟩
  haveI : LocallyCompactSpace (∀ v : S, GLoc σ J v) := Pi.locallyCompactSpace_of_finite
  haveI : LocallyCompactSpace (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) := Pi.locallyCompactSpace_of_finite
  haveI : LocallyCompactSpace (cent (proj σ J v₀ (ratEmb σ J γ))) := (isClosed_cent _).locallyCompactSpace
  refine GlobalTheory.T.quotient_measure_fibration (GLoc σ J v₀) (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) (∀ v : S, GLoc σ J v) (splitAt σ J S v₀)
    (cent (proj σ J v₀ (ratEmb σ J γ))) (cent (fun j : {j : S // j ≠ v₀} => proj σ J j (ratEmb σ J γ))) (cent (projAt σ J S (ratEmb σ J γ)))
    (fun a b => splitAt_mem_cent (projAt σ J S (ratEmb σ J γ)) a b) (isClosed_cent _) (isMulCommutative_cent_projAt σ J S hγ)
    dg dt μ Measure.haar _ (leftInv_integrand σ J S ff hCi) hint fun b => ?_
  set e := splitAt σ J S v₀
  have hsplit : (fun a => C (embAt σ J S (e (a, b))) *
      ∏ v : S, ff v ((e (a, b) v)⁻¹ * proj σ J v (ratEmb σ J γ) * e (a, b) v)) =
      fun a => (∏ j : {j : S // j ≠ v₀}, ff j ((b j)⁻¹ * proj σ J j (ratEmb σ J γ) * b j)) *
        (C (embAt σ J S (e (a, b))) * ff v₀ (a⁻¹ * proj σ J v₀ (ratEmb σ J γ) * a)) := by
    funext a
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [e, splitAt_self, splitAt_ne]
    ring
  have hmul : ∀ a a' : GLoc σ J v₀, e (a * a', b) = e (a, 1) * e (a', b) := fun a a' => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  refine (congrArg _ hsplit).trans ((quotInt_const_mul _ _ _ _ _).trans ?_)
  rw [hloc (fun a => C (embAt σ J S (e (a, b))))
    (hC.comp ((continuous_embAt σ J S).comp (e.continuous.comp (continuous_id.prodMk continuous_const))))
    (fun t ht a => by
      change C (embAt σ J S (e (t * a, b))) = C (embAt σ J S (e (a, b)))
      rw [hmul, map_mul, hCi _ (embAt_mem_cent σ J ((splitAt_mem_cent (projAt σ J S (ratEmb σ J γ)) t 1).2 ⟨ht, one_mem _⟩))])
    (fun g hg x => by
      change C (embAt σ J S (e (g * x, b))) = C (embAt σ J S (e (x, b)))
      rw [hmul, map_mul, show e (g, 1) = Pi.mulSingle v₀ g from splitAt_one g, embAt_mulSingle]
      exact hCP g hg _) Measure.haar, mul_zero]

end Gen3
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor

theorem typesFactor_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → (∀ v, (μf v).IsHaarMeasure) → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (Φ : WittFrame V) (u : SV (wittIndex V)) (γ : GF V), u ≠ 0 → IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → ∀ C : GA D V → ℂ, Continuous C → LeftInv (cent (rat V γ)) C → (∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C) → ∀ (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure] (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) * ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  intro hTC D V T U μf ff hff hHaar hH Φ u γ hu hγ hlevi C hC hCi hCN dg _ dt _
  classical
  obtain ⟨ε, hW, hε2, hεpos, hεlt, hεγ, hεN⟩ := GlobalTheory.T.levi_idempotent_splitting D V Φ u hu
  obtain ⟨v₀, hv₀⟩ := hH ε.rank hεpos hεlt
  have hfin := hff.isFinFamily.1
  exact hasQuotInt_integrand_zero (isCMExt_host D) (isHermND_gram V) T.S v₀ hγ ff
    (fun v => (hfin v).1.continuous) (fun v => (hfin v).2) (μf v₀) hC hCi
    (fun g => ε.map (T.frame v₀).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v₀).emb g).1 - 1) *
      (1 - ε.map (T.frame v₀).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v₀).emb g).1 - 1)
    (fun g hg y => hCN hW _ (hεN v₀ (T.frame v₀).emb g hg) y)
    (fun bf hbc hbi hbn ds _ => (GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish hTC D V T U μf ff hff v₀ (hHaar v₀) γ ε hγ hε2 (hεγ γ hlevi) hεpos hεlt
      hv₀ bf hbc hbi hbn ds).2) dg dt

end GlobalTheory.TypesFactor
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_semisimple_test_vanishing : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → (∀ v, (μf v).IsHaarMeasure) → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (Φ : WittFrame V) (u : SV (wittIndex V)) (γ : GF V), u ≠ 0 → IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → ∀ C : GA D V → ℂ, Continuous C → LeftInv (cent (rat V γ)) C → (∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C) → ∀ (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure] (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) * ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  atlas_forward_decl GlobalTheory.TypesFactor.typesFactor_vanish
end
