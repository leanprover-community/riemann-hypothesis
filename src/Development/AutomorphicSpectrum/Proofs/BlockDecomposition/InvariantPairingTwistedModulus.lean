import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous

section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirStable

section Det

variable {k : Type} [Field k]

end Det

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def zM (m : ℕ) (u : kˣ) : Mir k m := levi k m (Matrix.GeneralLinearGroup.scalar (Fin m) u)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def normInt [MeasurableSpace k] (ν : Measure k) (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (L : Set (Fin n → k)) (v : V) (v' : V') : ℂ :=
  (((piHaar ν n).real L : ℝ) : ℂ)⁻¹ * ∫ x in L, coef T B v v' x ∂(piHaar ν n)

section Int

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isAddHaar_piHaar (m : ℕ) : (piHaar ν m).IsAddHaarMeasure := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  unfold piHaar
  infer_instance

end Int

section Int

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

end Int

end Rep

end GlobalTheory.CompanionTheory.MirStable

end
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

theorem exists_vol_cosub {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) :
    ∃ vol : COSub k d → ℝ, (∀ L, 0 < vol L) ∧
      (∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S →
        vol L = (S.card : ℝ) * vol L') ∧
      ∀ (g : GL (Fin d) k) (L : COSub k d),
        ((vol (L.act g) : ℝ) : ℂ) ^ 2 * ((dpow d (-2) g : ℂˣ) : ℂ) = ((vol L : ℝ) : ℂ) ^ 2 := by
  classical
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  let ν : Measure k := Measure.addHaar
  haveI : ν.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure k).IsAddHaarMeasure
  haveI hμ : (piHaar ν d).IsAddHaarMeasure := GlobalTheory.CompanionTheory.MirStable.isAddHaar_piHaar ν d
  have hfin : ∀ L : COSub k d, piHaar ν d (L.sub : Set (Fin d → k)) ≠ ⊤ := fun L =>
    L.isCompact.measure_lt_top.ne
  have hne : ∀ L : COSub k d, piHaar ν d (L.sub : Set (Fin d → k)) ≠ 0 := fun L =>
    L.isOpen.measure_ne_zero _ ⟨0, L.sub.zero_mem⟩
  refine ⟨fun L => (piHaar ν d (L.sub : Set (Fin d → k))).toReal, fun L => ENNReal.toReal_pos (hne L) (hfin L), ?_, ?_⟩
  · intro L' L S hle hS
    have hU : (L.sub : Set (Fin d → k)) = ⋃ s ∈ S, {y | y - s ∈ L'.sub} := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe, exists_prop]
      constructor
      · intro hy
        obtain ⟨s, ⟨hs, hys⟩, -⟩ := hS.2 y hy
        exact ⟨s, hs, hys⟩
      · rintro ⟨s, hs, hys⟩
        have := L.sub.add_mem (hle hys) (hS.1 s hs)
        simpa using this
    have hdisj : Set.PairwiseDisjoint (S : Set (Fin d → k)) fun s => {y | y - s ∈ L'.sub} := by
      intro s hs t ht hst
      refine Set.disjoint_left.2 fun y hys hyt => hst ?_
      have hy : y ∈ L.sub := by
        have := L.sub.add_mem (hle hys) (hS.1 s hs)
        simpa using this
      exact (hS.2 y hy).unique ⟨hs, hys⟩ ⟨ht, hyt⟩
    have hcos : ∀ s : Fin d → k, piHaar ν d {y | y - s ∈ L'.sub} = piHaar ν d (L'.sub : Set (Fin d → k)) := by
      intro s
      have : {y | y - s ∈ L'.sub} = (fun y => y + (-s)) ⁻¹' (L'.sub : Set (Fin d → k)) := by
        ext y
        simp [sub_eq_add_neg]
      rw [this, measure_preimage_add_right]
    have hm : piHaar ν d (L.sub : Set (Fin d → k)) = (S.card : ENNReal) * piHaar ν d (L'.sub : Set (Fin d → k)) := by
      rw [hU, measure_biUnion_finset hdisj fun s _ => (isClopen_coset L' s).isOpen.measurableSet]
      simp [hcos]
    show (piHaar ν d (L.sub : Set (Fin d → k))).toReal = _
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  · intro g L
    have hI := setIntegral_inv_mulVec ν d g ((L.act g).sub : Set (Fin d → k)) (fun _ => (1 : ℂ))
    have hset : {y | (g : Matrix (Fin d) (Fin d) k) *ᵥ y ∈ ((L.act g).sub : Set (Fin d → k))} = (L.sub : Set (Fin d → k)) := by
      ext y
      exact COSub.mulVec_mem_act g
    rw [hset, setIntegral_const, setIntegral_const] at hI
    simp only [Measure.real, Complex.real_smul, mul_one] at hI
    have hn := nabs_pos' k (Matrix.GeneralLinearGroup.det g)
    have hd : ((dpow d (-2) g : ℂˣ) : ℂ) = (((nabs k (Matrix.GeneralLinearGroup.det g)) ^ (-2 : ℝ) : ℝ) : ℂ) := by
      simp only [dpow, detChar_apply]
      exact val_absPow_ofReal k (-2) _
    rw [hd, hI]
    have hr : (nabs k (Matrix.GeneralLinearGroup.det g)) ^ (-2 : ℝ) = ((nabs k (Matrix.GeneralLinearGroup.det g)) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hn.le, Real.rpow_two]
    rw [hr]
    have hn' : ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp

end GlobalTheory.CompanionTheory.BZCore

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_scaling_laws : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ), ∃ vol : COSub k d → ℝ, (∀ L, 0 < vol L) ∧ (∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → vol L = (S.card : ℝ) * vol L') ∧ ∀ (g : GL (Fin d) k) (L : COSub k d), ((vol (L.act g) : ℝ) : ℂ) ^ 2 * ((dpow d (-2) g : ℂˣ) : ℂ) = ((vol L : ℝ) : ℂ) ^ 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.exists_vol_cosub
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ind_eq_sum_reps {L' L : COSub k d} {S : Finset (Fin d → k)} (h : L'.sub ≤ L.sub) (hS : IsReps L' L S)
    (c : Fin d → k) (a : V) : ind L c a = ∑ s ∈ S, ind L' (c + s) a := by
  classical
  refine Subtype.ext (funext fun y => ?_)
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  show (ind L c a).1 y = ∑ s ∈ S, (ind L' (c + s) a).1 y
  simp only [ind_apply]
  have e : ∀ s, y - (c + s) = y - c - s := fun s => by abel
  simp only [e]
  by_cases hy : y - c ∈ L.sub
  · obtain ⟨s, ⟨hs, hys⟩, hu⟩ := hS.2 _ hy
    rw [if_pos hy, Finset.sum_eq_single s, if_pos hys]
    · intro t ht hts
      exact if_neg fun hm => hts (hu t ⟨ht, hm⟩)
    · exact fun hn => (hn hs).elim
  · rw [if_neg hy]
    refine (Finset.sum_eq_zero fun s hs => if_neg fun hm => hy ?_).symm
    simpa using L.sub.add_mem (h hm) (hS.1 s hs)

theorem mL_refine (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f') (L' L : COSub k d) (S : Finset (Fin d → k))
    (h : L'.sub ≤ L.sub) (hS : IsReps L' L S) (x : Fin d → k) (a : V) (a' : V') :
    mL B L x a a' = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
  classical
  have h1 : ∀ y, y ∈ L.sub → ∃ s, s ∈ S ∧ y - s ∈ L'.sub := fun y hy => (hS.2 y hy).exists
  choose! rep hrepS hrep using h1
  have uniq : ∀ y ∈ L.sub, ∀ s ∈ S, y - s ∈ L'.sub → rep y = s := fun y hy s hs hys =>
    (hS.2 y hy).unique ⟨hrepS y hy, hrep y hy⟩ ⟨hs, hys⟩
  have hshift : ∀ t ∈ S, ∑ s ∈ S, mL B L' (x + s - t) a a' = ∑ s ∈ S, mL B L' (x + s) a a' := by
    intro t ht
    have htL := hS.1 t ht
    have hm : ∀ s ∈ S, s - t ∈ L.sub := fun s hs => L.sub.sub_mem (hS.1 s hs) htL
    have hp : ∀ s ∈ S, s + t ∈ L.sub := fun s hs => L.sub.add_mem (hS.1 s hs) htL
    refine Finset.sum_nbij' (fun s => rep (s - t)) (fun s => rep (s + t)) (fun s hs => hrepS _ (hm s hs))
      (fun s hs => hrepS _ (hp s hs)) (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_)
    · refine uniq _ (L.sub.add_mem (hS.1 _ (hrepS _ (hm s hs))) htL) s hs ?_
      have := L'.sub.neg_mem (hrep _ (hm s hs))
      have e : rep (s - t) + t - s = -(s - t - rep (s - t)) := by abel
      rwa [e]
    · refine uniq _ (L.sub.sub_mem (hS.1 _ (hrepS _ (hp s hs))) htL) s hs ?_
      have := L'.sub.neg_mem (hrep _ (hp s hs))
      have e : rep (s + t) - t - s = -(s + t - rep (s + t)) := by abel
      rwa [e]
    · have e : x + s - t = x + rep (s - t) + (s - t - rep (s - t)) := by abel
      rw [e, mL_add_mem B L' _ (hrep _ (hm s hs))]
  calc mL B L x a a'
      = B (∑ s ∈ S, ind L' (x + s) a) (∑ t ∈ S, ind L' (0 + t) a') := by
        rw [mL, ← ind_eq_sum_reps h hS, ← ind_eq_sum_reps h hS]
    _ = ∑ t ∈ S, ∑ s ∈ S, mL B L' (x + s - t) a a' := by
        simp only [map_sum, LinearMap.sum_apply, B_ind_ind B hT, zero_add]
    _ = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
        rw [Finset.sum_congr rfl hshift, Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.BZCore

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_lattice_refinement_card : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ), (∀ x f f', B (shiftF x f) (shiftF x f') = B f f') → ∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S → ∀ (x : Fin d → k) (a : V) (a' : V'), mL B L x a a' = (S.card : ℂ) * ∑ s ∈ S, mL B L' (x + s) a a' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.mL_refine
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZCore

theorem isOpen_preserve_standard_lattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} :
    IsOpen {g : GL (Fin d) k | ∀ y ∈ (lat0 : COSub k d).sub,
      (g : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub} := by
  have hc : Continuous fun p : GL (Fin d) k × (Fin d → k) =>
      ((p.1 : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec p.2 :=
    Continuous.matrix_mulVec (Units.continuous_val.comp continuous_fst) continuous_snd
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hK : IsCompact ((lat0 : COSub k d).sub : Set (Fin d → k)) := lat0.isCompact
  exact hK.eventually_forall_of_forall_eventually
    (P := fun (h : GL (Fin d) k) (y : Fin d → k) =>
      (h : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub)
    fun y hy => hc.continuousAt.eventually_mem (lat0.isOpen.mem_nhds (hg y hy))

theorem isOpen_stabilizer_standard_lattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} :
    IsOpen {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} := by
  have h1 := isOpen_preserve_standard_lattice (k := k) (d := d)
  have h2 := h1.preimage (continuous_inv (G := GL (Fin d) k))
  convert h1.inter h2 using 1
  ext g
  constructor
  · intro hg
    have hg' : (lat0 : COSub k d).act g = lat0 := hg
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have := (COSub.mulVec_mem_act (L := (lat0 : COSub k d)) g (y := y)).2 hy
      rwa [hg'] at this
    · have hy' : y ∈ ((lat0 : COSub k d).act g).sub := by rwa [hg']
      exact COSub.mem_act.1 hy'
  · rintro ⟨ha, hb⟩
    refine COSub.ext (AddSubgroup.ext fun y => ?_)
    rw [COSub.mem_act]
    refine ⟨fun hy => ?_, fun hy => hb y hy⟩
    have := ha _ hy
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this

end GlobalTheory.CompanionTheory.BZCore
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_standard_lattice_stabilizer : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}, IsOpen {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.isOpen_stabilizer_standard_lattice
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem latZ_subset_of_mem_nhds (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) {A : Set (Fin d → k)} (hA : A ∈ 𝓝 (0 : Fin d → k)) :
    ∃ r : ℕ, ∀ y, y ∈ (latZ z (r : ℤ)).sub → y ∈ A := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ A := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : A ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by simpa using hA
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ A := hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rwa [h2] at h1

theorem vecMulVec_single_mul_self (i : Fin d) (u : Fin d → k) :
    vecMulVec u (Pi.single i (1 : k)) * vecMulVec u (Pi.single i (1 : k)) =
      u i • vecMulVec u (Pi.single i (1 : k)) := by
  ext a b
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
  simp
  split_ifs <;> simp [mul_comm]

theorem exists_mem_nhds_one_mulVec_eq (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (U : Set (GL (Fin d) k))
    (hU : U ∈ 𝓝 (1 : GL (Fin d) k)) (x : Fin d → k) (hx : x ≠ 0) :
    ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub →
      ∃ g ∈ U, (g : Matrix (Fin d) (Fin d) k).mulVec x = y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let P : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => vecMulVec (y - x) (Pi.single i (1 : k))
  let M : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => 1 + (x i)⁻¹ • P y
  let N : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => 1 - (y i)⁻¹ • P y
  have hPc : Continuous P := (continuous_id.sub continuous_const).matrix_vecMulVec continuous_const
  have hPx : P x = 0 := by
    ext a b
    simp [P, vecMulVec_apply]
  have hMc : ContinuousAt M x := by
    have h : Continuous fun y => (1 : Matrix (Fin d) (Fin d) k) + (x i)⁻¹ • P y := by fun_prop
    exact h.continuousAt
  have hNc : ContinuousAt N x := by
    have h1 : ContinuousAt (fun y : Fin d → k => (y i)⁻¹) x := (continuous_apply i).continuousAt.inv₀ hi
    have h2 : ContinuousAt (fun y => (y i)⁻¹ • P y) x := h1.fun_smul hPc.continuousAt
    have h3 : ContinuousAt (fun y => (1 : Matrix (Fin d) (Fin d) k) - (y i)⁻¹ • P y) x := continuousAt_const.fun_sub h2
    exact h3
  have hMx : M x = 1 := by simp [M, hPx]
  have hNx : N x = 1 := by simp [N, hPx]
  have hMN : ∀ y, y i ≠ 0 → M y * N y = 1 := by
    intro y hy
    have hsq : P y * P y = (y i - x i) • P y := by
      simpa [P] using vecMulVec_single_mul_self i (y - x)
    simp only [M, N, mul_sub, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul]
    have h3 : (y i)⁻¹ + ((y i)⁻¹ * ((x i)⁻¹ * y i) - (y i)⁻¹ * ((x i)⁻¹ * x i)) = (x i)⁻¹ := by
      field_simp
      ring
    rw [← add_smul, h3, add_sub_cancel_right]
  have hNM : ∀ y, y i ≠ 0 → N y * M y = 1 := fun y hy => mul_eq_one_comm.1 (hMN y hy)
  have hMv : ∀ y, (M y).mulVec x = y := by
    intro y
    have h1 : (P y).mulVec x = x i • (y - x) := by
      ext a
      simp [P, vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    simp only [M, Matrix.add_mulVec, one_mulVec, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hi, one_smul]
    abel
  have hT : Filter.Tendsto (fun y => (M y, MulOpposite.op (N y))) (𝓝 x)
      (𝓝 (Units.embedProduct (Matrix (Fin d) (Fin d) k) 1)) := by
    have e : Units.embedProduct (Matrix (Fin d) (Fin d) k) 1 = (M x, MulOpposite.op (N x)) := by
      rw [hMx, hNx, map_one]
      rfl
    rw [e]
    exact hMc.tendsto.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hNc.tendsto)
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  have hgood : ∀ᶠ y in 𝓝 x, y i ≠ 0 ∧ (M y, MulOpposite.op (N y)) ∈ W :=
    ((continuous_apply i).continuousAt.eventually_ne hi).and (hT.eventually hW)
  have hA : {l : Fin d → k | (x + l) i ≠ 0 ∧ (M (x + l), MulOpposite.op (N (x + l))) ∈ W} ∈ 𝓝 (0 : Fin d → k) := by
    have hc : Filter.Tendsto (fun l : Fin d → k => x + l) (𝓝 0) (𝓝 x) := by
      have h : Continuous fun l : Fin d → k => x + l := by fun_prop
      simpa using h.tendsto 0
    exact hc.eventually hgood
  obtain ⟨s, hs⟩ := latZ_subset_of_mem_nhds z ϖ hz hϖ hϖ0 hA
  refine ⟨s, fun y hy => ?_⟩
  have hy' := hs _ hy
  rw [Set.mem_setOf_eq, add_sub_cancel] at hy'
  refine ⟨⟨M y, N y, hMN y hy'.1, hNM y hy'.1⟩, hWU ?_, hMv y⟩
  exact hy'.2

end GlobalTheory.CompanionTheory.BZCore

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_orbit_GL_near_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (U : Set (GL (Fin d) k)), U ∈ 𝓝 (1 : GL (Fin d) k) → ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∃ g ∈ U, (g : Matrix (Fin d) (Fin d) k).mulVec x = y := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.exists_mem_nhds_one_mulVec_eq
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore.MaxPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem exists_pow_val_lt {ϖ : k} (hϖ : ValuativeRel.valuation k ϖ < 1) (γ : ValuativeRel.ValueGroupWithZero k)
    (hγ : γ ≠ 0) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ValuativeRel.valuation k ϖ ^ n < γ := by
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
  exact ⟨n, fun m hm => lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn⟩

theorem latZ_add (z : GL (Fin d) k) (a b : ℤ) : latZ z (a + b) = (latZ z b).act (z ^ a) := by
  rw [latZ, latZ, COSub.act_act, _root_.zpow_add]

theorem smul_mem_latZ (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0) (a b : ℤ)
    (w : Fin d → k) : ϖ ^ a • w ∈ (latZ z (a + b)).sub ↔ w ∈ (latZ z b).sub := by
  rw [latZ_add, ← zpow_mulVec z ϖ hz hϖ0 a w]
  exact COSub.mulVec_mem_act _

theorem scale_step (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) (x : Fin d → k) : F (latZ z (r + 1)) (ϖ • x) = F (latZ z r) x := by
  have h := hS (latZ z r) x
  have e : (latZ z r).act z = latZ z (r + 1) := by
    rw [add_comm, latZ_add, zpow_one]
  rw [e, hz, Matrix.smul_mulVec, one_mulVec] at h
  exact h

theorem scale (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0)
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) : ∀ x : Fin d → k, F (latZ z r) (ϖ ^ r • x) = F (latZ z 0) x := by
  induction r using Int.induction_on with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [zpow_add₀ hϖ0, zpow_one, mul_comm, mul_smul, scale_step z ϖ hz F hS, ih]
  | pred n ih =>
    intro x
    have h := scale_step z ϖ hz F hS (-(n : ℤ) - 1) (ϖ ^ (-(n : ℤ) - 1) • x)
    rw [sub_add_cancel, smul_smul, ← zpow_one_add₀ hϖ0, add_sub_cancel, ih] at h
    exact h.symm

theorem scale_inv (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0)
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) (y : Fin d → k) : F (latZ z r) y = F (latZ z 0) (ϖ ^ (-r) • y) := by
  rw [← scale z ϖ hz hϖ0 F hS r, smul_smul, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, one_smul]

theorem shell_unif (z : GL (Fin d) k) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hN : ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r →
      F (latZ z (r : ℤ)) y = c) :
    ∃ r₁ : ℕ, ∀ y : Fin d → k, y ∈ (latZ z 0).sub → y ∉ (latZ z 1).sub → ∀ r : ℕ, r₁ ≤ r →
      F (latZ z (r : ℤ)) y = c := by
  have hK : IsCompact (((latZ z 0).sub : Set (Fin d → k)) \ ((latZ z 1).sub : Set (Fin d → k))) :=
    (latZ z 0).isCompact.diff (latZ z 1).isOpen
  have h := hK.induction_on
    (p := fun A => ∃ s : ℕ, ∀ y ∈ A, ∀ r : ℕ, s ≤ r → F (latZ z (r : ℤ)) y = c)
    ⟨0, by simp⟩
    (fun A B hAB ⟨s, hs⟩ => ⟨s, fun y hy => hs y (hAB hy)⟩)
    (fun A B ⟨s, hs⟩ ⟨t, ht⟩ => ⟨max s t, fun y hy r hr => hy.elim
      (fun h => hs y h r (le_trans (le_max_left _ _) hr))
      (fun h => ht y h r (le_trans (le_max_right _ _) hr))⟩)
    (by
      intro x hx
      have hx0 : x ≠ 0 := fun h => hx.2 (h ▸ (latZ z 1).sub.zero_mem)
      obtain ⟨s, hs⟩ := hN x hx0
      exact ⟨{y | y - x ∈ (latZ z (s : ℤ)).sub},
        mem_nhdsWithin_of_mem_nhds ((isClopen_coset _ x).isOpen.mem_nhds
          (by simp [(latZ z (s : ℤ)).sub.zero_mem])), s, fun y hy r hr => hs y hy r hr⟩)
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun y h0 h1 r hr => hs y ⟨h0, h1⟩ r hr⟩

theorem exists_shell (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (w : Fin d → k) (hw : w ≠ 0) :
    ∃ m : ℤ, w ∈ (latZ z m).sub ∧ w ∉ (latZ z (m + 1)).sub := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hvi : ValuativeRel.valuation k (w i) ≠ 0 := by simpa using hi
  have hv : 0 < ValuativeRel.valuation k ϖ := zero_lt_iff.2 (by simpa using hϖ0)
  have hbdd : ∃ b : ℤ, ∀ m : ℤ, w ∈ (latZ z m).sub → m ≤ b := by
    obtain ⟨N, hN⟩ := exists_pow_val_lt hϖ _ hvi
    refine ⟨N, fun m hm => ?_⟩
    by_contra hlt
    have hm0 : 0 ≤ m := by omega
    lift m to ℕ using hm0
    have h1 := (mem_latZ z ϖ hz hϖ0 _ w).1 hm i
    rw [zpow_natCast] at h1
    exact absurd h1 (not_le.2 (hN m (by omega)))
  have hinh : ∃ m : ℤ, w ∈ (latZ z m).sub := by
    have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ j, ValuativeRel.valuation k (w j) ≤
        (ValuativeRel.valuation k ϖ ^ n)⁻¹ := by
      refine Filter.eventually_all.2 fun j => ?_
      by_cases hj : ValuativeRel.valuation k (w j) = 0
      · exact Filter.Eventually.of_forall fun n => by rw [hj]; exact zero_le'
      · obtain ⟨N, hN⟩ := exists_pow_val_lt hϖ _ (inv_ne_zero hj)
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        exact (le_inv_comm₀ (zero_lt_iff.2 hj) (pow_pos hv n)).2 (hN n hn).le
    obtain ⟨n, hn⟩ := hall.exists
    refine ⟨-(n : ℤ), (mem_latZ z ϖ hz hϖ0 _ w).2 fun j => ?_⟩
    rw [_root_.zpow_neg, zpow_natCast]
    exact hn j
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  exact ⟨m, hm, fun h => absurd (hmax _ h) (by omega)⟩

theorem far (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r₁ : ℕ)
    (hr₁ : ∀ y : Fin d → k, y ∈ (latZ z 0).sub → y ∉ (latZ z 1).sub → ∀ r : ℕ, r₁ ≤ r →
      F (latZ z (r : ℤ)) y = c)
    (w : Fin d → k) (hw : w ∉ (latZ z (-(r₁ : ℤ))).sub) : F (latZ z 0) w = c := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ (latZ z (-(r₁ : ℤ))).sub.zero_mem)
  obtain ⟨m, hm, hm1⟩ := exists_shell z ϖ hz hϖ hϖ0 w hw0
  have hlt : m < -(r₁ : ℤ) := by
    by_contra hge
    exact hw (latZ_anti z ϖ hz hϖ hϖ0 _ _ (not_lt.1 hge) hm)
  have h0 : ϖ ^ (-m) • w ∈ (latZ z 0).sub := by
    have := (smul_mem_latZ z ϖ hz hϖ0 (-m) m w).2 hm
    rwa [neg_add_cancel] at this
  have h1 : ϖ ^ (-m) • w ∉ (latZ z 1).sub := by
    intro h
    have e : (1 : ℤ) = -m + (m + 1) := by ring
    rw [e] at h
    exact hm1 ((smul_mem_latZ z ϖ hz hϖ0 (-m) (m + 1) w).1 h)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = -m := ⟨(-m).toNat, by omega⟩
  have h2 := hr₁ _ h0 h1 t (by omega)
  rw [ht, scale z ϖ hz hϖ0 F hS] at h2
  exact h2

theorem exists_vector_standard_lattice_not_sub {hd : 0 < d} (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) :
    ∃ e : Fin d → k, e ∈ (latZ z 0).sub ∧ e ∉ (latZ z 1).sub := by
  classical
  refine ⟨Pi.single ⟨0, hd⟩ 1, (mem_latZ z ϖ hz hϖ0 _ _).2 fun j => ?_, fun h => ?_⟩
  · rw [zpow_zero, Pi.single_apply]
    split_ifs <;> simp
  · have h1 := (mem_latZ z ϖ hz hϖ0 _ _).1 h ⟨0, hd⟩
    rw [zpow_one, Pi.single_eq_same, map_one] at h1
    exact absurd h1 (not_le.2 hϖ)

theorem eq_const_standard_lattice_refining (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hR : Refines F) (hP : ∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r₁ : ℕ)
    (hfar : ∀ w : Fin d → k, w ∉ (latZ z (-(r₁ : ℤ))).sub → F (latZ z 0) w = c) (x : Fin d → k) :
    F (latZ z 0) x = c := by
  classical
  have hcont : Continuous (F (latZ z 0)) := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
    filter_upwards [(isClopen_coset (latZ z 0) x).isOpen.mem_nhds
      (by simp [(latZ z 0).sub.zero_mem])] with y hy
    have h := hP (latZ z 0) x (y - x) hy
    rwa [add_sub_cancel] at h
  obtain ⟨xs, -, hmax⟩ := (latZ z (-(r₁ : ℤ))).isCompact.exists_isMaxOn
    ⟨0, (latZ z (-(r₁ : ℤ))).sub.zero_mem⟩
    (f := fun x => ‖F (latZ z 0) x - c‖) (hcont.sub continuous_const).norm.continuousOn
  set M : ℝ := ‖F (latZ z 0) xs - c‖ with hM
  have hall : ∀ x, ‖F (latZ z 0) x - c‖ ≤ M := by
    intro x
    by_cases hx : x ∈ (latZ z (-(r₁ : ℤ))).sub
    · exact hmax hx
    · rw [hfar x hx, sub_self, norm_zero]
      exact norm_nonneg _
  have hle : (latZ z ((r₁ + 1 : ℕ) : ℤ)).sub ≤ (latZ z 0).sub :=
    latZ_anti z ϖ hz hϖ hϖ0 _ _ (by positivity)
  have hle1 : (latZ z ((r₁ + 1 : ℕ) : ℤ)).sub ≤ (latZ z 1).sub :=
    latZ_anti z ϖ hz hϖ hϖ0 _ _ (by push_cast; omega)
  obtain ⟨S, hSr⟩ := exists_reps _ _ hle
  have hsum := hR _ _ S hle hSr xs
  obtain ⟨e, he0, he1⟩ := exists_vector_standard_lattice_not_sub (hd := hd) z ϖ hz hϖ hϖ0
  have hex : ∃ s ∈ S, xs + s ∉ (latZ z 1).sub := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s0, ⟨hs0, h0⟩, -⟩ := hSr.2 0 (latZ z 0).sub.zero_mem
    obtain ⟨s1, ⟨hs1, h1⟩, -⟩ := hSr.2 e he0
    apply he1
    have e' : e = (e - s1) + (xs + s1) - (xs + s0) - (0 - s0) := by abel
    rw [e']
    exact (latZ z 1).sub.sub_mem ((latZ z 1).sub.sub_mem ((latZ z 1).sub.add_mem (hle1 h1) (hcon s1 hs1))
      (hcon s0 hs0)) (hle1 h0)
  obtain ⟨ss, hss, hss1⟩ := hex
  let t : (Fin d → k) → ℂ := fun s => F (latZ z 0) (ϖ ^ (-((r₁ + 1 : ℕ) : ℤ)) • (xs + s)) - c
  have hts : t ss = 0 := by
    have hn : ϖ ^ (-((r₁ + 1 : ℕ) : ℤ)) • (xs + ss) ∉ (latZ z (-(r₁ : ℤ))).sub := by
      intro h
      have e' : -(r₁ : ℤ) = -((r₁ + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [e'] at h
      exact hss1 ((smul_mem_latZ z ϖ hz hϖ0 _ 1 _).1 h)
    simp only [t]
    rw [hfar _ hn, sub_self]
  have hid : (S.card : ℂ) * (F (latZ z 0) xs - c) = ∑ s ∈ S, t s := by
    simp only [t, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_sub, hsum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => scale_inv z ϖ hz hϖ0 F hS _ _
  have h1 : (S.card : ℝ) * M ≤ ∑ s ∈ S, ‖t s‖ := by
    have := norm_sum_le S t
    rw [← hid, norm_mul, Complex.norm_natCast] at this
    exact this
  have h2 : M ≤ ∑ s ∈ S, (M - ‖t s‖) := by
    have := Finset.single_le_sum (f := fun s => M - ‖t s‖) (fun s _ => sub_nonneg.2 (hall _)) hss
    simpa [hts] using this
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  have hM0 : M ≤ 0 := by linarith
  have := (hall x).trans hM0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem eq_const (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hR : Refines F) (hP : ∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (hN : ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r →
      F (latZ z (r : ℤ)) y = c) (r : ℕ) (x : Fin d → k) : F (latZ z (r : ℤ)) x = c := by
  obtain ⟨r₁, hr₁⟩ := shell_unif z F c hN
  rw [scale_inv z ϖ hz hϖ0 F hS]
  exact eq_const_standard_lattice_refining hd z ϖ hz hϖ hϖ0 F c hR hP hS r₁ (far z ϖ hz hϖ hϖ0 F c hS r₁ hr₁) _

end GlobalTheory.CompanionTheory.BZCore.MaxPrin

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximum_principle_lattice_functions : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ), Refines F → (∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x) → (∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x) → (∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r → F (latZ z (r : ℤ)) y = c) → ∀ (r : ℕ) (x : Fin d → k), F (latZ z (r : ℤ)) x = c := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_latZ_subset_of_mem_nhds (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) {U : Set (Fin d → k)} (hU : U ∈ 𝓝 (0 : Fin d → k)) :
    ∃ r : ℕ, ((latZ z (r : ℤ)).sub : Set (Fin d → k)) ⊆ U := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ U := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : U ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by simpa using hU
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ U :=
    hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ)
      ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rwa [h2] at h1

theorem exists_latZ_invariant (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V) :
    ∃ r₀ : ℕ, ∀ y, ∀ l ∈ (latZ z (r₀ : ℤ)).sub, f.1 (y + l) = f.1 y := by
  have hlc : IsLocallyConstant f.1 := f.2.1
  have hK : IsCompact (tsupport f.1) := f.2.2
  have hW : ∀ᶠ l : Fin d → k in 𝓝 0, ∀ y ∈ tsupport f.1, f.1 (y + l) = f.1 y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun p : (Fin d → k) × (Fin d → k) => p.2 + p.1 := continuous_snd.add continuous_fst
    have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc.comp_continuous hc) ((0 : Fin d → k), y)
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hlc.comp_continuous continuous_snd)
      ((0 : Fin d → k), y)
    filter_upwards [h1, h2] with p hp1 hp2
    have e1 : f.1 (p.2 + p.1) = f.1 (y + 0) := hp1
    have e2 : f.1 p.2 = f.1 y := hp2
    rw [e1, e2, add_zero]
  obtain ⟨r₀, hr₀⟩ := exists_latZ_subset_of_mem_nhds z ϖ hz hϖ hϖ0 hW
  refine ⟨r₀, fun y l hl => ?_⟩
  by_cases hy : y ∈ tsupport f.1
  · exact hr₀ hl y hy
  by_cases hyl : y + l ∈ tsupport f.1
  · have := hr₀ ((latZ z (r₀ : ℤ)).sub.neg_mem hl) (y + l) hyl
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyl]

theorem exists_eq_sum_ind_of_invariant (L : COSub k d) (f : SchF k d V)
    (hf : ∀ y, ∀ l ∈ L.sub, f.1 (y + l) = f.1 y) :
    ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind L p.1 p.2 := by
  classical
  have hK : IsCompact (tsupport f.1) := f.2.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : Fin d → k => {y | y - c ∈ L.sub})
    (fun c => (isClopen_coset L c).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  let mk : (Fin d → k) → (Fin d → k) ⧸ L.sub := QuotientAddGroup.mk
  have hmk : ∀ (q : (Fin d → k) ⧸ L.sub) (y : Fin d → k), y - Quotient.out q ∈ L.sub ↔ mk y = q := by
    intro q y
    have e : mk (Quotient.out q) = q := QuotientAddGroup.out_eq' q
    constructor
    · intro h
      rw [← e]
      exact (QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using h)).symm
    · intro h
      have h' : mk (Quotient.out q) = mk y := e.trans h.symm
      simpa [sub_eq_add_neg, add_comm] using QuotientAddGroup.eq.1 h'
  let Q : Finset ((Fin d → k) ⧸ L.sub) := t.image mk
  let φ : ((Fin d → k) ⧸ L.sub) → (Fin d → k) × V := fun q => (Quotient.out q, f.1 (Quotient.out q))
  have hφ : Function.Injective φ := fun q q' h => by
    have h1 : Quotient.out q = Quotient.out q' := congrArg Prod.fst h
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', h1]
  refine ⟨Q.image φ, Subtype.ext (funext fun y => ?_)⟩
  rw [Finset.sum_image hφ.injOn, Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ Q, ((ind L (φ q).1 (φ q).2 : SchF k d V) : (Fin d → k) → V) y =
      if mk y = q then f.1 y else 0 := by
    intro q _
    show (ind L (φ q).1 (φ q).2).1 y = _
    rw [ind_apply]
    by_cases h : mk y = q
    · have hm : y - Quotient.out q ∈ L.sub := (hmk q y).2 h
      rw [if_pos hm, if_pos h]
      have := hf (Quotient.out q) _ hm
      rw [add_sub_cancel] at this
      exact this.symm
    · rw [if_neg (fun hm => h ((hmk q y).1 hm)), if_neg h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hy
  · rfl
  · refine image_eq_zero_of_notMem_tsupport fun hyK => hy ?_
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hyK)
    have hc' : y - c ∈ L.sub := hc
    have : mk y = mk c := (QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using hc')).symm
    rw [this]
    exact Finset.mem_image_of_mem mk hct

theorem schF_eq_sum_ind (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind (latZ z (r : ℤ)) p.1 p.2 := by
  obtain ⟨r₀, hr₀⟩ := exists_latZ_invariant z ϖ hz hϖ hϖ0 f
  refine ⟨r₀, fun r hr => exists_eq_sum_ind_of_invariant _ f fun y l hl => hr₀ y l ?_⟩
  exact latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr) hl

end GlobalTheory.CompanionTheory.BZCore

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_function_lattice_indicator_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (f : SchF k d V), ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → ∃ I : Finset ((Fin d → k) × V), f = ∑ p ∈ I, ind (latZ z (r : ℤ)) p.1 p.2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.schF_eq_sum_ind
end

section
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

theorem exists_gl_mulVec_eq {k : Type} [Field k] {d : ℕ} (e x : Fin d → k) (he : e ≠ 0) (hx : x ≠ 0) :
    ∃ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = x := by
  obtain ⟨u, hu⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton k (Fin d → k) e he).symm.trans
      (LinearEquiv.toSpanNonzeroSingleton k (Fin d → k) x hx))
  have h1 := hu ⟨e, Submodule.mem_span_singleton_self e⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one k (Fin d → k) e he, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  have hAB : LinearMap.toMatrix' u.toLinearMap * LinearMap.toMatrix' u.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have hBA : LinearMap.toMatrix' u.symm.toLinearMap * LinearMap.toMatrix' u.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨LinearMap.toMatrix' u.toLinearMap, LinearMap.toMatrix' u.symm.toLinearMap, hAB, hBA⟩, ?_⟩
  show (LinearMap.toMatrix' u.toLinearMap).mulVec e = x
  rw [LinearMap.toMatrix'_mulVec]
  exact h1.symm

theorem exists_bilin_eventual {V V' ι : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (l : Filter ι) [l.NeBot] (G : V → V' → ι → ℂ)
    (h1 : ∀ a b a' i, G (a + b) a' i = G a a' i + G b a' i)
    (h2 : ∀ a a' b' i, G a (a' + b') i = G a a' i + G a b' i)
    (h3 : ∀ (t : ℂ) a a' i, G (t • a) a' i = t * G a a' i)
    (h4 : ∀ (t : ℂ) a a' i, G a (t • a') i = t * G a a' i)
    (H : ∀ a a', ∃ v : ℂ, ∀ᶠ i in l, G a a' i = v) :
    ∃ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ, ∀ a a', ∀ᶠ i in l, G a a' i = β a a' := by
  choose v hv using H
  have f1 : ∀ a b a', v (a + b) a' = v a a' + v b a' := by
    intro a b a'
    obtain ⟨i, e1, e2, e3⟩ := ((hv (a + b) a').and ((hv a a').and (hv b a'))).exists
    rw [← e1, ← e2, ← e3, h1]
  have f2 : ∀ (t : ℂ) a a', v (t • a) a' = t • v a a' := by
    intro t a a'
    obtain ⟨i, e1, e2⟩ := ((hv (t • a) a').and (hv a a')).exists
    rw [← e1, ← e2, h3, smul_eq_mul]
  have f3 : ∀ a a' b', v a (a' + b') = v a a' + v a b' := by
    intro a a' b'
    obtain ⟨i, e1, e2, e3⟩ := ((hv a (a' + b')).and ((hv a a').and (hv a b'))).exists
    rw [← e1, ← e2, ← e3, h2]
  have f4 : ∀ (t : ℂ) a a', v a (t • a') = t • v a a' := by
    intro t a a'
    obtain ⟨i, e1, e2⟩ := ((hv a (t • a')).and (hv a a')).exists
    rw [← e1, ← e2, h4, smul_eq_mul]
  exact ⟨LinearMap.mk₂ ℂ v f1 f2 f3 f4, fun a a' => hv a a'⟩

theorem refines_const_on_coset {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {d : ℕ} (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (hF : Refines F)
    (s₀ : ℕ) (x : Fin d → k)
    (H : ∀ (r : ℕ) (y : Fin d → k), y - x ∈ (latZ z (s₀ : ℤ)).sub → F (latZ z (r : ℤ)) y = F (latZ z (r : ℤ)) x)
    (y : Fin d → k) (hy : y - x ∈ (latZ z (s₀ : ℤ)).sub) (L : COSub k d) (hL : L.sub ≤ (latZ z (s₀ : ℤ)).sub) :
    F L y = F (latZ z (s₀ : ℤ)) x := by
  classical
  obtain ⟨r, hr⟩ := latZ_basis z ϖ hz hϖ hϖ0 L
  have key : ∀ (M : COSub k d), (latZ z (r : ℤ)).sub ≤ M.sub → M.sub ≤ (latZ z (s₀ : ℤ)).sub →
      ∀ w : Fin d → k, w - x ∈ (latZ z (s₀ : ℤ)).sub → F M w = F (latZ z (r : ℤ)) x := by
    intro M hM hM' w hw
    obtain ⟨S, hS⟩ := exists_reps _ M hM
    have hcard : (S.card : ℂ) ≠ 0 := by
      obtain ⟨s, hs, -⟩ := hS.2 0 M.sub.zero_mem
      exact_mod_cast (Finset.card_pos.2 ⟨s, hs.1⟩).ne'
    have h1 := hF _ M S hM hS w
    have h2 : ∑ s ∈ S, F (latZ z (r : ℤ)) (w + s) = ∑ _s ∈ S, F (latZ z (r : ℤ)) x := by
      refine Finset.sum_congr rfl fun s hs => H r (w + s) ?_
      have e : w + s - x = (w - x) + s := by abel
      rw [e]
      exact AddSubgroup.add_mem _ hw (hM' (hS.1 s hs))
    rw [h2, Finset.sum_const, nsmul_eq_mul] at h1
    exact mul_left_cancel₀ hcard h1
  rw [key L hr hL y hy, key _ (hr.trans hL) le_rfl x (by rw [sub_self]; exact AddSubgroup.zero_mem _)]

theorem shift_invariant_of_exact_twist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V') (hX : IsSmooth X) (hY : IsSmooth Y)
    (P : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hP : ∀ g a a', P (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * P a a')
    (e : Fin d → k) (he : e ≠ 0)
    (hU : ∀ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = e → ∀ a a', β (X g a) (Y g a') =
        ((dpow d (-2) g : ℂˣ) : ℂ) * β a a') → ∃ c : ℂ, ∀ a a', β a a' = c * P a a')
    (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (ω ω' : ℂ) (hω : ∀ a, X z a = ω • a) (hω' : ∀ a, Y z a = ω' • a)
    (hωω : ω * ω' = ((dpow d (-2) z : ℂˣ) : ℂ))
    (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f')
    (hG : ∀ g f f', B (actF X g f) (actF Y g f') = B f f'),
    ∀ f f' x, B f (shiftF x f') = B f f' := by
  intro k _ _ _ _ d hd V V' _ _ _ _ X Y hX hY P hP e he hU z ϖ hz hϖ hϖ0 ω ω' hω hω' hωω B hT hG
  obtain ⟨vol, hv0, hvR, hvG⟩ := GlobalTheory.T.lattice_volume_scaling_laws (k := k) d
  have hvC : ∀ L, ((vol L : ℝ) : ℂ) ≠ 0 := fun L => by exact_mod_cast (hv0 L).ne'

  let F : V → V' → COSub k d → (Fin d → k) → ℂ := fun a a' L x => mL B L x a a' / ((vol L : ℝ) : ℂ) ^ 2
  have hFdef : ∀ a a' L x, F a a' L x = mL B L x a a' / ((vol L : ℝ) : ℂ) ^ 2 := fun _ _ _ _ => rfl
  have hRef : ∀ a a', Refines (F a a') := by
    intro a a' L' L S h hS x
    have hcard : (S.card : ℂ) ≠ 0 := by
      obtain ⟨s, hs, -⟩ := hS.2 0 L.sub.zero_mem
      exact_mod_cast (Finset.card_pos.2 ⟨s, hs.1⟩).ne'
    have hv : ((vol L : ℝ) : ℂ) = (S.card : ℂ) * ((vol L' : ℝ) : ℂ) := by
      rw [hvR L' L S h hS]; push_cast; rfl
    simp only [hFdef]
    rw [GlobalTheory.T.pairing_lattice_refinement_card B hT L' L S h hS x a a', hv, ← Finset.sum_div]
    have := hvC L'
    field_simp
  have hPer : ∀ a a' (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F a a' L (x + l) = F a a' L x := by
    intro a a' L x l hl
    simp only [hFdef, mL_add_mem B L x hl]
  have hAct : ∀ (g : GL (Fin d) k) a a' (L : COSub k d) (x : Fin d → k),
      F (X g a) (Y g a') (L.act g) ((g : Matrix (Fin d) (Fin d) k).mulVec x) =
        ((dpow d (-2) g : ℂˣ) : ℂ) * F a a' L x := by
    intro g a a' L x
    simp only [hFdef]
    rw [mL_act X Y B hG, ← hvG g L]
    have h1 := hvC (L.act g)
    have h2 := (dpow d (-2) g : ℂˣ).ne_zero
    field_simp
  have hScale : ∀ a a' (L : COSub k d) (x : Fin d → k),
      F a a' (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F a a' L x := by
    intro a a' L x
    have h := hAct z a a' L x
    rw [hω, hω', ← hωω] at h
    have h0 : ω * ω' ≠ 0 := by rw [hωω]; exact (dpow d (-2) z : ℂˣ).ne_zero
    simp only [hFdef, mL_smul_left, mL_smul_right] at h ⊢
    apply mul_left_cancel₀ h0
    rw [← h]
    ring
  have hComm : ∀ (g : GL (Fin d) k) (r : ℤ), g * z ^ r = z ^ r * g := by
    intro g r
    have : Commute g z := by
      apply Units.ext
      show (g : Matrix (Fin d) (Fin d) k) * (z : Matrix (Fin d) (Fin d) k) = (z : Matrix (Fin d) (Fin d) k) * g
      rw [hz]
      simp
    exact (this.zpow_right r).eq
  have hLat : ∀ (g : GL (Fin d) k), (lat0 : COSub k d).act g = lat0 → ∀ r : ℤ, (latZ z r).act g = latZ z r := by
    intro g hg r
    rw [latZ, COSub.act_act, hComm, ← COSub.act_act, hg]

  have hLoc : ∀ a a' (x : Fin d → k), x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub →
      ∀ L : COSub k d, L.sub ≤ (latZ z (s : ℤ)).sub → F a a' L y = F a a' (latZ z (s : ℤ)) x := by
    intro a a' x hx
    have hU1 : {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} ∩ ({g | X g a = a} ∩ {g | Y g a' = a'}) ∈
        𝓝 (1 : GL (Fin d) k) := by
      refine ((GlobalTheory.T.isOpen_standard_lattice_stabilizer (k := k) (d := d)).inter ((hX a).inter (hY a'))).mem_nhds ?_
      exact ⟨COSub.act_one _, by simp, by simp⟩
    obtain ⟨s, hs⟩ := GlobalTheory.T.local_orbit_GL_near_one z ϖ hz hϖ hϖ0 _ hU1 x hx
    refine ⟨s, refines_const_on_coset z ϖ hz hϖ hϖ0 (F a a') (hRef a a') s x fun r y hy => ?_⟩
    obtain ⟨g, ⟨hg, hga, hga'⟩, rfl⟩ := hs y hy
    have hd1 : ((dpow d (-2) g : ℂˣ) : ℂ) = 1 := by
      have h := hvG g lat0
      rw [hg] at h
      have h1 := hvC lat0
      exact mul_left_cancel₀ (pow_ne_zero 2 h1) (by rw [h, mul_one])
    have h := hAct g a a' (latZ z (r : ℤ)) x
    rw [hga, hga', hLat g hg, hd1, one_mul] at h
    exact h
  have hβ : ∀ x : Fin d → k, x ≠ 0 → ∃ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ, ∀ a a', ∃ s : ℕ, ∀ y : Fin d → k,
      y - x ∈ (latZ z (s : ℤ)).sub → ∀ L : COSub k d, L.sub ≤ (latZ z (s : ℤ)).sub → F a a' L y = β a a' := by
    intro x hx
    obtain ⟨β, hb⟩ := exists_bilin_eventual (Filter.atTop : Filter ℕ) (fun a a' r => F a a' (latZ z (r : ℤ)) x)
      (fun a b a' r => by simp only [hFdef, mL_add_left, add_div])
      (fun a a' b' r => by simp only [hFdef, mL_add_right, add_div])
      (fun t a a' r => by simp only [hFdef, mL_smul_left, mul_div_assoc])
      (fun t a a' r => by simp only [hFdef, mL_smul_right, mul_div_assoc])
      (fun a a' => by
        obtain ⟨s, hs⟩ := hLoc a a' x hx
        refine ⟨F a a' (latZ z (s : ℤ)) x, Filter.eventually_atTop.2 ⟨s, fun r hr => ?_⟩⟩
        exact hs x (by simp) _ (latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr)))
    refine ⟨β, fun a a' => ?_⟩
    obtain ⟨s, hs⟩ := hLoc a a' x hx
    obtain ⟨r, hr⟩ := Filter.eventually_atTop.1 (hb a a')
    refine ⟨s, fun y hy L hL => ?_⟩
    rw [hs y hy L hL, ← hr (max r s) (le_max_left _ _)]
    exact (hs x (by simp) _ (latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast le_max_right r s))).symm
  choose! β hβ using hβ
  have hEq : ∀ (g : GL (Fin d) k) (x : Fin d → k), x ≠ 0 → ∀ a a',
      β ((g : Matrix (Fin d) (Fin d) k).mulVec x) (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * β x a a' := by
    intro g x hx a a'
    have hgx : (g : Matrix (Fin d) (Fin d) k).mulVec x ≠ 0 := by
      intro h0
      apply hx
      have := congrArg (fun y => ((g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) h0
      simpa [mulVec_mulVec, ← Units.val_mul] using this
    obtain ⟨s₁, h₁⟩ := hβ x hx a a'
    obtain ⟨s₂, h₂⟩ := hβ _ hgx (X g a) (Y g a')
    obtain ⟨r, hr⟩ := latZ_basis z ϖ hz hϖ hϖ0 ((latZ z (s₂ : ℤ)).act g⁻¹)
    let t : ℕ := max r s₁
    have ht₁ : (latZ z (t : ℤ)).sub ≤ (latZ z (s₁ : ℤ)).sub :=
      latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast le_max_right r s₁)
    have ht₂ : ((latZ z (t : ℤ)).act g).sub ≤ (latZ z (s₂ : ℤ)).sub := by
      have ht : (latZ z (t : ℤ)).sub ≤ (latZ z (r : ℤ)).sub :=
        latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast le_max_left r s₁)
      have h := COSub.act_mono (ht.trans hr) g
      rwa [COSub.act_act, mul_inv_cancel, COSub.act_one] at h
    rw [← h₂ ((g : Matrix (Fin d) (Fin d) k).mulVec x) (by rw [sub_self]; exact AddSubgroup.zero_mem _) _ ht₂, hAct,
      h₁ x (by rw [sub_self]; exact AddSubgroup.zero_mem _) _ ht₁]
  obtain ⟨c₀, hc₀⟩ := hU (β e) (fun g hg a a' => by
    have := hEq g e he a a'
    rwa [hg] at this)
  have hβc : ∀ x : Fin d → k, x ≠ 0 → ∀ a a', β x a a' = c₀ * P a a' := by
    intro x hx a a'
    obtain ⟨g, rfl⟩ := exists_gl_mulVec_eq e x he hx
    have h := hEq g e he (X g⁻¹ a) (Y g⁻¹ a')
    have e1 : ∀ b, X g (X g⁻¹ b) = b := fun b => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : ∀ b, Y g (Y g⁻¹ b) = b := fun b => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1, e2, hc₀, hP] at h
    rw [h]
    have h3 : ((dpow d (-2) g : ℂˣ) : ℂ) * ((dpow d (-2) g⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    calc _ = (((dpow d (-2) g : ℂˣ) : ℂ) * ((dpow d (-2) g⁻¹ : ℂˣ) : ℂ)) * (c₀ * P a a') := by ring
      _ = _ := by rw [h3, one_mul]
  have hAll : ∀ (r : ℕ) (x : Fin d → k) a a', mL B (latZ z (r : ℤ)) x a a' =
      c₀ * P a a' * ((vol (latZ z (r : ℤ)) : ℝ) : ℂ) ^ 2 := by
    intro r x a a'
    have h := GlobalTheory.T.maximum_principle_lattice_functions hd z ϖ hz hϖ hϖ0 (F a a') (c₀ * P a a') (hRef a a') (hPer a a') (hScale a a')
      (fun x hx => by
        obtain ⟨s, hs⟩ := hβ x hx a a'
        refine ⟨s, fun y hy r hr => ?_⟩
        rw [hs y hy _ (latZ_anti z ϖ hz hϖ hϖ0 _ _ (by exact_mod_cast hr)), hβc x hx]) r x
    rw [hFdef, div_eq_iff (pow_ne_zero 2 (hvC _))] at h
    exact h
  intro f f' x
  obtain ⟨r₁, h₁⟩ := GlobalTheory.T.schwartz_function_lattice_indicator_sum z ϖ hz hϖ hϖ0 f
  obtain ⟨r₂, h₂⟩ := GlobalTheory.T.schwartz_function_lattice_indicator_sum z ϖ hz hϖ hϖ0 f'
  obtain ⟨I, hI⟩ := h₁ (max r₁ r₂) (le_max_left _ _)
  obtain ⟨I', hI'⟩ := h₂ (max r₁ r₂) (le_max_right _ _)
  rw [hI, hI']
  simp only [map_sum, LinearMap.sum_apply, shiftF_ind, B_ind_ind B hT, hAll]

end GlobalTheory.CompanionTheory.BZCore

end
end

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_twisted_modulus : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (X : Representation ℂ (GL (Fin d) k) V) (Y : Representation ℂ (GL (Fin d) k) V') (hX : IsSmooth X) (hY : IsSmooth Y)
    (P : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hP : ∀ g a a', P (X g a) (Y g a') = ((dpow d (-2) g : ℂˣ) : ℂ) * P a a')
    (e : Fin d → k) (he : e ≠ 0)
    (hU : ∀ β : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
      (∀ g : GL (Fin d) k, (g : Matrix (Fin d) (Fin d) k).mulVec e = e → ∀ a a', β (X g a) (Y g a') =
        ((dpow d (-2) g : ℂˣ) : ℂ) * β a a') → ∃ c : ℂ, ∀ a a', β a a' = c * P a a')
    (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (ω ω' : ℂ) (hω : ∀ a, X z a = ω • a) (hω' : ∀ a, Y z a = ω' • a)
    (hωω : ω * ω' = ((dpow d (-2) z : ℂˣ) : ℂ))
    (B : SchF k d V →ₗ[ℂ] SchF k d V' →ₗ[ℂ] ℂ)
    (hT : ∀ x f f', B (shiftF x f) (shiftF x f') = B f f')
    (hG : ∀ g f f', B (actF X g f) (actF Y g f') = B f f'),
    ∀ f f' x, B f (shiftF x f') = B f f' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BZCore.shift_invariant_of_exact_twist
end
