import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne
import BuildAid.ForwardExisting

section
section
open Filter Topology

namespace GlobalTheory.WeilM

theorem SB.exists_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type}
    (L : ι → AddSubgroup X) (hL : ∀ i, IsOpen (L i : Set X)) (hb : ∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) :
    ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y := by
    intro Y
    have h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0) := by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl
    have h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X) := (continuous_add_left Y).continuousAt.preimage_mem_nhds h1
    obtain ⟨i, hi⟩ := hb _ h2
    exact ⟨i, fun C hC => hi hC⟩
  choose g hg using key
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)})
    (fun Y => (hL _).preimage (continuous_sub_right Y))
    (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)
  have hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem
  obtain ⟨j, hj⟩ := hb _ hW
  refine ⟨j, fun Y C hC => ?_⟩
  have hCt : ∀ Y0 ∈ t, C ∈ L (g Y0) := fun Y0 h0 => by
    have := hj hC
    simp only [Set.mem_iInter] at this
    exact this Y0 h0
  by_cases h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)
  · obtain ⟨Y0, h0, hY⟩ := h
    have e1 := hg Y0 _ hY
    have e2 := hg Y0 _ (add_mem hY (hCt Y0 h0))
    rw [show Y0 + (Y - Y0) = Y by abel] at e1
    rw [show Y0 + (Y - Y0 + C) = Y + C by abel] at e2
    rw [e1, e2]
  · push_neg at h
    have hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0) := fun Z hZ => by
      have := ht hZ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨Y0, h0, h1⟩ := this
      exact ⟨Y0, h0, h1⟩
    have hY : Y ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn Y hZ
      exact h Y0 h0 h1
    have hYC : Y + C ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn _ hZ
      apply h Y0 h0
      have := sub_mem h1 (hCt Y0 h0)
      rwa [show Y + C - Y0 - C = Y - Y0 by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]

end GlobalTheory.WeilM
end

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroup_periodic : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type} (L : ι → AddSubgroup X), (∀ i, IsOpen (L i : Set X)) → (∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) → ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  atlas_forward_decl GlobalTheory.WeilM.SB.exists_periodic
end

section
section
open Filter Topology

namespace GlobalTheory.LinSchur

open Classical in

theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur

example : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y :=
  fun L hL f hf hp => GlobalTheory.LinSchur.exists_finset_eq_sum_cind L hL f hf hp
end

open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  atlas_forward_decl GlobalTheory.LinSchur.exists_finset_eq_sum_cind
end

section
open Filter Topology ValuativeRel

noncomputable section

namespace GlobalTheory.LinSchurLatt

theorem eq_one_of_pow_near (z : ℂ) (h : ∀ m : ℕ, ‖z ^ m - 1‖ ≤ 1 / 2) : z = 1 := by
  have hre : ∀ m : ℕ, 1 / 2 ≤ (z ^ m).re := by
    intro m
    have h1 := (Complex.abs_re_le_norm (z ^ m - 1)).trans (h m)
    rw [Complex.sub_re, Complex.one_re] at h1
    linarith [(abs_le.1 h1).1]
  have hS : ∀ N : ℕ, (N : ℝ) / 2 ≤ ‖∑ m ∈ Finset.range N, z ^ m‖ := by
    intro N
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ m ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun m _ => hre m
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have e := geom_sum_mul z N
  have h2 : ‖z - 1‖ * ((N : ℝ) / 2) ≤ 1 / 2 := by
    calc ‖z - 1‖ * ((N : ℝ) / 2) ≤ ‖z - 1‖ * ‖∑ m ∈ Finset.range N, z ^ m‖ :=
          mul_le_mul_of_nonneg_left (hS N) hpos.le
      _ = ‖z ^ N - 1‖ := by rw [← e, norm_mul, mul_comm]
      _ ≤ 1 / 2 := h N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_natCast_le_one (m : ℕ) : valuation k (m : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (natCast_mem (valuation k).integer m)

theorem ker_int_mem_nhds (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) :
    {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} ∈ 𝓝 (0 : k) := by
  have hO : IsCompact {x : k | valuation k x ≤ 1} := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hU : {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} ∈ 𝓝 (0 : k) := by
    have h1 : Metric.closedBall (ψ0 0) (1 / 2) ∈ 𝓝 (ψ0 0) := Metric.closedBall_mem_nhds _ (by norm_num)
    filter_upwards [hc.continuousAt.preimage_mem_nhds h1] with u hu
    simpa [Metric.mem_closedBall, dist_eq_norm, AddChar.map_zero_eq_one] using hu
  have hev : ∀ᶠ w in 𝓝 (0 : k), ∀ a ∈ {x : k | valuation k x ≤ 1}, a * w ∈ {u : k | ‖ψ0 u - 1‖ ≤ 1 / 2} := by
    refine hO.eventually_forall_of_forall_eventually fun a _ => ?_
    have hcm : Continuous fun z : k × k => z.2 * z.1 := continuous_snd.mul continuous_fst
    have h0 : (fun z : k × k => z.2 * z.1) (0, a) = 0 := by simp
    exact hcm.continuousAt.preimage_mem_nhds (by simpa using hU)
  filter_upwards [hev] with w hw o ho
  apply eq_one_of_pow_near
  intro m
  have hmo : valuation k ((m : k) * o) ≤ 1 := by
    rw [map_mul]
    exact mul_le_one' (valuation_natCast_le_one m) ho
  have h1 := hw _ hmo
  have h2 : (m : k) * o * w = m • (o * w) := by rw [nsmul_eq_mul, mul_assoc]
  rwa [h2, AddChar.map_nsmul_eq_pow] at h1

theorem ker_int_lt {ψ0 : AddChar k ℂ} {t : k} (ht : ψ0 t ≠ 1) {u : k}
    (hu : ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1) : valuation k u < valuation k t := by
  by_contra h
  push_neg at h
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply ht
    have : t = 0 := by simpa using h
    rw [this, AddChar.map_zero_eq_one]
  have hvu : valuation k u ≠ 0 := by simpa using hu0
  apply ht
  have hle : valuation k (t / u) ≤ 1 := by
    rw [map_div₀, div_eq_mul_inv]
    calc valuation k t * (valuation k u)⁻¹ ≤ valuation k u * (valuation k u)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hvu
  have := hu (t / u) hle
  rwa [div_mul_cancel₀ _ hu0] at this

theorem nhdsNE_neBot' : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_ball_mat (n d : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} := by
  have : {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ γ} =
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem exists_smul_int_mem' (n d : ℕ) (W : Set (Matrix (Fin n) (Fin d) k)) (hW : W ∈ 𝓝 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) k, (∀ i j, valuation k (x i j) ≤ 1) → c • x ∈ W := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ 1}, c • x ∈ W := by
    refine (isCompact_ball_mat n d 1).eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have h0 : (fun z : k × Matrix (Fin n) (Fin d) k => z.1 • z.2) (0, y) = 0 := by simp
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hW)
  haveI := nhdsNE_neBot' (k := k)
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and
    (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

end GlobalTheory.LinSchurLatt

namespace GlobalTheory.LinSchurLatt

theorem latt_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  intro k _ _ _ _ n d ψ0 hc hne
  obtain ⟨t, ht⟩ : ∃ t, ψ0 t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (AddChar.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ0)
  have hvt : valuation k t ≠ 0 := by simpa using ht0
  have hK := ker_int_mem_nhds ψ0 hc
  refine ⟨fun s hs => ⟨?_, ?_⟩, fun W hW => ?_⟩
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hev : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ i j,
        s * Y i j ∈ {u : k | ∀ o : k, valuation k o ≤ 1 → ψ0 (o * u) = 1} := by
      refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
      have hcont : Continuous fun Y : Matrix (Fin n) (Fin d) k => s * Y i j :=
        continuous_const.mul (continuous_id.matrix_elem i j)
      exact hcont.continuousAt.preimage_mem_nhds (by simpa using hK)
    filter_upwards [hev] with Y hY
    exact GlobalTheory.LinSchur.mem_latt.2 fun i j o ho => hY i j o ho
  · have hsub : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆
        {x : Matrix (Fin n) (Fin d) k | ∀ i j, valuation k (x i j) ≤ valuation k t * (valuation k s)⁻¹} := by
      intro Y hY i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have hvs : valuation k s ≠ 0 := by simpa using hs
      rw [map_mul] at h1
      calc valuation k (Y i j) = valuation k s * valuation k (Y i j) * (valuation k s)⁻¹ := by
            rw [mul_comm (valuation k s), mul_assoc, mul_inv_cancel₀ hvs, mul_one]
        _ ≤ valuation k t * (valuation k s)⁻¹ := by gcongr
    have hcl : IsClosed (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) := by
      have e : (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) =
          ⋂ i, ⋂ j, ⋂ o : {o : k // valuation k o ≤ 1}, {Y | ψ0 (o.1 * (s * Y i j)) = 1} := by
        ext Y
        simp only [SetLike.mem_coe, GlobalTheory.LinSchur.mem_latt, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall]
      rw [e]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun o =>
        isClosed_eq (hc.comp (continuous_const.mul (continuous_const.mul (continuous_id.matrix_elem i j))))
          continuous_const
    exact (isCompact_ball_mat n d _).of_isClosed_subset hcl hsub
  · obtain ⟨c, hc0, hcW⟩ := exists_smul_int_mem' n d W hW
    refine ⟨t / c, div_ne_zero ht0 hc0, fun Y hY => ?_⟩
    have hx : ∀ i j, valuation k ((c⁻¹ • Y) i j) ≤ 1 := by
      intro i j
      have h1 := ker_int_lt ht fun o ho => GlobalTheory.LinSchur.mem_latt.1 hY i j o ho
      have e : (c⁻¹ • Y) i j = (t / c * Y i j) * t⁻¹ := by
        rw [Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [e, map_mul, map_inv₀]
      calc valuation k (t / c * Y i j) * (valuation k t)⁻¹ ≤ valuation k t * (valuation k t)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hvt
    have := hcW _ hx
    rwa [smul_smul, mul_inv_cancel₀ hc0, one_smul] at this

end GlobalTheory.LinSchurLatt
end
end

section
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  first | exact @GlobalTheory.LinSchurLatt.latt_open_compact_basis | exact GlobalTheory.LinSchurLatt.latt_open_compact_basis | (intros; apply GlobalTheory.LinSchurLatt.latt_open_compact_basis <;> assumption)
end

section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem dual {k : Type} [Field k] [ValuativeRel k] {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k}
    {Y : Matrix (Fin n) (Fin d) k} (hY : Y ∉ latt ψ0 n d s) :
    ∃ l : Matrix (Fin n) (Fin d) k →ₗ[k] k, (∀ Z ∈ latt ψ0 n d s, ψ0 (l Z) = 1) ∧ ψ0 (l Y) ≠ 1 := by
  rw [mem_latt] at hY
  push_neg at hY
  obtain ⟨i, j, o, ho, h⟩ := hY
  let l : Matrix (Fin n) (Fin d) k →ₗ[k] k :=
    { toFun := fun Z => o * (s * Z i j)
      map_add' := fun a b => by simp only [Matrix.add_apply]; ring
      map_smul' := fun c a => by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  exact ⟨l, fun Z hZ => hZ i j o ho, h⟩

theorem cind_mem {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {L : AddSubgroup X}
    (ho : IsOpen (L : Set X)) (hc : IsCompact (L : Set X)) (y : X) : cind L y ∈ GlobalTheory.WeilM.SB X := by
  have hK : IsOpen {Z : X | Z - y ∈ L} := ho.preimage (continuous_sub_right y)
  have hKc : IsClosed {Z : X | Z - y ∈ L} := (AddSubgroup.isClosed_of_isOpen L ho).preimage (continuous_sub_right y)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro Y
    by_cases hY : Y - y ∈ L
    · exact ⟨_, hK, hY, fun Z hZ => by simp only [cind, if_pos (show Z - y ∈ L from hZ), if_pos hY]⟩
    · exact ⟨_, hKc.isOpen_compl, hY, fun Z hZ => by simp only [cind, if_neg (show Z - y ∉ L from hZ), if_neg hY]⟩
  · have himg : {Z : X | Z - y ∈ L} = (fun Z => Z + y) '' (L : Set X) := by
      ext Z
      constructor
      · intro h
        exact ⟨Z - y, h, sub_add_cancel Z y⟩
      · rintro ⟨W, hW, rfl⟩
        show W + y - y ∈ L
        rwa [add_sub_cancel_right]
    refine IsCompact.of_isClosed_subset (himg ▸ hc.image (continuous_add_right y)) (isClosed_tsupport _)
      (closure_minimal ?_ hKc)
    intro Z hZ
    by_contra h
    exact hZ (by simp only [cind, if_neg (show Z - y ∉ L from h)])

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have e := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

end GlobalTheory.LinSchur

open GlobalTheory.LinSchur in

theorem GlobalTheory.LinSchur.eq_smul_of_commute : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)) (ι₂ : Xt → Matrix (Fin n) (Fin d) k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → Xt → Xt) (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n d Xt _ _ V ψ0 hcont hne ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  classical
  obtain ⟨hLoc, hBasis⟩ := GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis n d ψ0 hcont hne
  have inj : ∀ x ∈ V, ∀ y ∈ V, ι₁ x = ι₁ y → x = y := fun x hx y hy h => hbij.injOn hx hy h
  have surj : ∀ f ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k), ∃ x, x ∈ V ∧ ι₁ x = f := fun f hf => hbij.surjOn hf
  have maps : ∀ x ∈ V, ι₁ x ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := fun x hx => hbij.mapsTo hx
  have h20 : ι₂ 0 = 0 := by
    have e := hlin 0 V.zero_mem 0 V.zero_mem 1
    simpa using e
  have hsmul : ∀ x ∈ V, ∀ c : ℂ, ι₂ (c • x) = c • ι₂ x := by
    intro x hx c
    have e := hlin x hx 0 V.zero_mem c
    rwa [add_zero, h20, add_zero] at e
  have hsum : ∀ (F : Finset (Matrix (Fin n) (Fin d) k)) (a : Matrix (Fin n) (Fin d) k → ℂ)
      (xs : Matrix (Fin n) (Fin d) k → Xt), (∀ y ∈ F, xs y ∈ V) →
      ι₂ (∑ y ∈ F, a y • xs y) = ∑ y ∈ F, a y • ι₂ (xs y) := by
    intro F a xs hxs
    induction F using Finset.induction_on with
    | empty => simpa using h20
    | insert y F hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy, hlin _ (hxs y (Finset.mem_insert_self _ _)) _
        (V.sum_mem fun z hz => V.smul_mem _ (hxs z (Finset.mem_insert_of_mem hz))),
        ih fun z hz => hxs z (Finset.mem_insert_of_mem hz)]
  have stepB : ∀ x ∈ V, ∀ C, (∀ Y, ι₁ x (Y + C) = ι₁ x Y) → ∀ Y, ι₂ x (Y + C) = ι₂ x Y := by
    intro x hx C hper Y
    obtain ⟨h1, h2, h3⟩ := hTr C x hx
    have e0 : Tr C x = x := inj _ h1 _ hx (by rw [h2]; funext Y; exact hper Y)
    have e := congrFun h3 Y
    rw [e0] at e
    exact e.symm
  have stepA : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ∀ Y, Y - y ∉ latt ψ0 n d s → ι₂ x Y = 0 := by
    intro s x hx y hxy Y hY
    obtain ⟨l, hl1, hl2⟩ := dual hY
    obtain ⟨m1, m2, m3⟩ := hMu l x hx
    have e1 : ι₁ (Mu l x) = ι₁ (ψ0 (l y) • x) := by
      rw [m2, map_smul, hxy]
      funext Z
      simp only [cind, Pi.smul_apply, smul_eq_mul]
      split_ifs with hZ
      · rw [mul_one, mul_one, show l Z = l (Z - y) + l y by rw [← map_add, sub_add_cancel],
          AddChar.map_add_eq_mul, hl1 _ hZ, one_mul]
      · simp
    have e2 : Mu l x = ψ0 (l y) • x := inj _ m1 _ (V.smul_mem _ hx) e1
    have e3 := congrFun m3 Y
    rw [e2, hsmul x hx] at e3
    simp only [Pi.smul_apply, smul_eq_mul] at e3
    have hYy : ψ0 (l Y) = ψ0 (l (Y - y)) * ψ0 (l y) := by
      rw [← AddChar.map_add_eq_mul, ← map_add, sub_add_cancel]
    rw [hYy] at e3
    have e4 : ψ0 (l y) * (1 - ψ0 (l (Y - y))) * ι₂ x Y = 0 := by linear_combination e3
    rcases mul_eq_zero.mp e4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (addChar_ne_zero ψ0 _)
      · exact absurd (sub_eq_zero.mp h).symm hl2
    · exact h
  have stepC : ∀ s : k, ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y → ι₂ x = ι₂ x y • ι₁ x := by
    intro s x hx y hxy
    funext Y
    rw [hxy]
    simp only [cind, Pi.smul_apply, smul_eq_mul]
    split_ifs with hY
    · rw [mul_one]
      have e := stepB x hx (Y - y) (fun Z => by
        rw [hxy]
        simp only [cind]
        rw [show Z + (Y - y) - y = (Z - y) + (Y - y) by abel, (latt ψ0 n d s).add_mem_cancel_right hY]) y
      rwa [add_sub_cancel] at e
    · rw [mul_zero]
      exact stepA s x hx y hxy Y hY
  have hcind : ∀ s : k, s ≠ 0 → ∀ y, cind (latt ψ0 n d s) y ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) :=
    fun s hs y => cind_mem (hLoc s hs).1 (hLoc s hs).2 y
  choose! xs hxsV hxs1 using fun s (hs : s ≠ 0) y => surj _ (hcind s hs y)
  have stepD : ∀ s : k, s ≠ 0 → ∀ x ∈ V, ∀ y, ι₁ x = cind (latt ψ0 n d s) y →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx y hxy
    rw [stepC s x hx y hxy]
    congr 1
    obtain ⟨t1, t2, t3⟩ := hTr y x hx
    have e0 : Tr y x = xs s 0 := inj _ t1 _ (hxsV s hs 0) (by
      rw [t2, hxs1 s hs 0, hxy]
      funext Z
      simp only [cind, add_sub_cancel_right, sub_zero])
    have e := congrFun t3 0
    rw [e0, zero_add] at e
    exact e.symm
  have stepE : ∀ s : k, s ≠ 0 → ∀ x ∈ V, (∀ Y, ∀ C ∈ latt ψ0 n d s, ι₁ x (Y + C) = ι₁ x Y) →
      ι₂ x = ι₂ (xs s 0) 0 • ι₁ x := by
    intro s hs x hx hper
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator _ (hLoc s hs).1 (ι₁ x) (maps x hx) hper
    have hxeq : x = ∑ y ∈ F, ι₁ x y • xs s y :=
      inj _ hx _ (V.sum_mem fun y _ => V.smul_mem _ (hxsV s hs y)) (by
        rw [map_sum]
        simp only [map_smul, hxs1 s hs]
        exact hF)
    calc ι₂ x = ι₂ (∑ y ∈ F, ι₁ x y • xs s y) := congrArg ι₂ hxeq
      _ = ∑ y ∈ F, ι₁ x y • ι₂ (xs s y) := hsum F _ _ (fun y _ => hxsV s hs y)
      _ = ∑ y ∈ F, ι₁ x y • (ι₂ (xs s 0) 0 • cind (latt ψ0 n d s) y) :=
          Finset.sum_congr rfl fun y _ => by
            rw [stepD s hs (xs s y) (hxsV s hs y) y (hxs1 s hs y), hxs1 s hs y]
      _ = ι₂ (xs s 0) 0 • ∑ y ∈ F, ι₁ x y • cind (latt ψ0 n d s) y := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun y _ => smul_comm _ _ _
      _ = ι₂ (xs s 0) 0 • ι₁ x := by rw [← hF]
  have stepF : ∀ s : k, s ≠ 0 → ∀ s' : k, s' ≠ 0 →
      (latt ψ0 n d s' : Set (Matrix (Fin n) (Fin d) k)) ⊆ latt ψ0 n d s →
      ι₂ (xs s 0) 0 = ι₂ (xs s' 0) 0 := by
    intro s hs s' hs' hsub
    have e0 := stepE s' hs' (xs s 0) (hxsV s hs 0) (fun Y C hC => by
      rw [hxs1 s hs 0]
      simp only [cind, sub_zero, (latt ψ0 n d s).add_mem_cancel_right (hsub hC)])
    have e := congrFun e0 0
    rw [hxs1 s hs 0] at e
    simpa [cind] using e
  refine ⟨ι₂ (xs 1 0) 0, fun x hx => ?_⟩
  obtain ⟨⟨s, hs⟩, hper⟩ := GlobalTheory.T.exists_openSubgroup_periodic (fun s : {s : k // s ≠ 0} => latt ψ0 n d s) (fun s => (hLoc s.1 s.2).1)
    (fun W hW => by
      obtain ⟨s, hs, h⟩ := hBasis W hW
      exact ⟨⟨s, hs⟩, h⟩) (ι₁ x) (maps x hx)
  rw [stepE s hs x hx hper]
  congr 1
  obtain ⟨s'', hs'', hsub⟩ := hBasis ((latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∩ latt ψ0 n d 1)
    (inter_mem ((hLoc s hs).1.mem_nhds (latt ψ0 n d s).zero_mem) ((hLoc 1 one_ne_zero).1.mem_nhds (latt ψ0 n d 1).zero_mem))
  rw [stepF s hs s'' hs'' (fun z hz => (hsub hz).1), stepF 1 one_ne_zero s'' hs'' (fun z hz => (hsub hz).2)]
end
end
