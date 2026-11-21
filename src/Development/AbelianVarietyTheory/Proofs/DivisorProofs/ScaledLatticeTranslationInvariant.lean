import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothPeriodicPartitionOfUnity
import BuildAid.ForwardExisting
import GroundTheory.GlobalFields.TateThesis.LatticePoisson
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

section
section
open Filter
open scoped SchwartzMap Topology

namespace GlobalTheory
namespace SchwartzSum

theorem hasSum_of_summable_seminorms :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  intro V _ _ _ ι u hu
  have hS : Summable u := by
    rw [summable_iff_vanishing]
    intro e he
    obtain ⟨⟨S, r⟩, hr, hsub⟩ := (schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball.mem_iff.1 he
    simp only at hr hsub
    have hg : Summable (fun i => ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i)) :=
      summable_sum fun kn _ => hu kn.1 kn.2
    obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.1 hg) r hr
    refine ⟨s, fun t ht => hsub ?_⟩
    rw [Seminorm.mem_ball_zero]
    have h1 := hs t ht
    calc (S.sup (schwartzSeminormFamily ℂ V ℂ)) (∑ i ∈ t, u i)
        ≤ ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (∑ i ∈ t, u i) :=
          Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun kn hkn =>
            Finset.single_le_sum (f := fun kn => schwartzSeminormFamily ℂ V ℂ kn (∑ i ∈ t, u i))
              (fun _ _ => apply_nonneg _ _) hkn
      _ ≤ ∑ kn ∈ S, ∑ i ∈ t, schwartzSeminormFamily ℂ V ℂ kn (u i) :=
          Finset.sum_le_sum fun kn _ =>
            Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
      _ = ∑ i ∈ t, ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i) := Finset.sum_comm
      _ ≤ ‖∑ i ∈ t, ∑ kn ∈ S, schwartzSeminormFamily ℂ V ℂ kn (u i)‖ := Real.le_norm_self _
      _ < r := h1
  refine ⟨∑' i, u i, fun x => ?_, fun T => hS.hasSum.mapL T⟩
  have h := hS.hasSum.mapL ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ))
  simpa using h

end SchwartzSum
end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_schwartz_series : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type}
    (u : ι → SchwartzMap V ℂ), (∀ k n : ℕ, Summable (fun i => SchwartzMap.seminorm ℂ k n (u i))) →
    ∃ F : SchwartzMap V ℂ, (∀ x, HasSum (fun i => u i x) (F x)) ∧
      ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, HasSum (fun i => T (u i)) (T F) := by
  atlas_forward_decl GlobalTheory.SchwartzSum.hasSum_of_summable_seminorms
end

section
section
open scoped ContDiff Topology

namespace GlobalTheory.LatticeSumOne

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_radius (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ R : ℝ, ∀ x : V, ∃ l : Λ, ‖x + l‖ ≤ R := by
  obtain ⟨t, ht⟩ := GlobalTheory.PeriodicPartition.exists_finite_subcover Λ
    (fun k : V => {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1})
    (fun k => by
      have : {z : V | ∃ l : Λ, z + l ∈ Metric.ball k 1} =
          ⋃ l : Λ, (fun z : V => z + l) ⁻¹' Metric.ball k 1 := by
        ext z; simp
      rw [this]
      exact isOpen_iUnion fun l => Metric.isOpen_ball.preimage (by fun_prop))
    (fun k l z hz => by
      obtain ⟨m, hm⟩ := hz
      refine ⟨m - l, ?_⟩
      simpa [add_sub_cancel, add_assoc, sub_eq_add_neg] using hm)
    (fun z => ⟨z, 0, by simp⟩)
  refine ⟨1 + ∑ k ∈ t, ‖k‖, fun x => ?_⟩
  obtain ⟨k, hk, l, hl⟩ := ht x
  refine ⟨l, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hl
  have h1 : ‖k‖ ≤ ∑ k ∈ t, ‖k‖ := Finset.single_le_sum (f := fun k => ‖k‖) (fun _ _ => norm_nonneg _) hk
  calc ‖x + l‖ = ‖(x + l - k) + k‖ := by abel_nf
    _ ≤ ‖x + l - k‖ + ‖k‖ := norm_add_le _ _
    _ ≤ 1 + ∑ k ∈ t, ‖k‖ := by linarith

theorem exists_schwartz_lattice_sum_one (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  obtain ⟨R, hR⟩ := exists_radius Λ
  set R' : ℝ := max R 1 with hR'
  let φ : ContDiffBump (0 : V) := ⟨R', R' + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  have hφc : HasCompactSupport (φ : V → ℝ) := φ.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (φ : V → ℝ) := φ.contDiff
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => φ.nonneg
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate Λ (φ : V → ℝ) hφc
  set S : V → ℝ := fun z => ∑ᶠ l : Λ, φ (z + l) with hSdef
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : Λ) (z : V) => φ (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSper : ∀ (l : Λ) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hR z
    have h1 := single_le_finsum (f := fun m : Λ => φ (z + m)) l (hlf.point_finite z)
      (fun m => hφ0 _)
    have h2 : φ (z + l) = 1 := φ.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hl.trans (le_max_left _ _))
    have : 1 ≤ S z := by rw [← h2]; exact h1
    linarith
  set g : V → ℂ := fun z => ((φ z * (S z)⁻¹ : ℝ) : ℂ) with hgdef
  have hgc : HasCompactSupport g := by
    have : HasCompactSupport (fun z => φ z * (S z)⁻¹) := hφc.mul_right
    exact this.comp_left (g := Complex.ofReal) (by simp)
  have hgs : ContDiff ℝ ∞ g :=
    Complex.ofRealCLM.contDiff.comp (hφs.mul (hSs.inv fun z => (hSpos z).ne'))
  refine ⟨hgc.toSchwartzMap hgs, hgc, fun x => ?_⟩
  have hfin := hlf.point_finite x
  have hval : ∀ l : Λ, (hgc.toSchwartzMap hgs) (x + l) = ((φ (x + l) : ℝ) : ℂ) * ((S x)⁻¹ : ℝ) := by
    intro l
    show g (x + l) = _
    simp only [hgdef, hSper, Complex.ofReal_mul]
  simp_rw [hval]
  have hsum : HasSum (fun l : Λ => ((φ (x + l) : ℝ) : ℂ) * (((S x)⁻¹ : ℝ) : ℂ))
      (∑ l ∈ hfin.toFinset, ((φ (x + l) : ℝ) : ℂ) * (((S x)⁻¹ : ℝ) : ℂ)) :=
    hasSum_sum_of_ne_finset_zero fun l hl => by
      have : φ (x + l) = 0 := by
        by_contra hne
        exact hl (hfin.mem_toFinset.2 hne)
      simp [this]
  convert hsum using 1
  have hS : S x = ∑ l ∈ hfin.toFinset, φ (x + l) :=
    finsum_eq_sum_of_support_subset (fun l : Λ => φ (x + l)) (fun l hl => hfin.mem_toFinset.2 hl)
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← hS, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (hSpos x).ne', Complex.ofReal_one]

end GlobalTheory.LatticeSumOne

namespace GlobalTheory

theorem exists_schwartz_hasCompactSupport_latticeTranslates_sum_one :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  intro V _ _ _ Λ _ _
  exact LatticeSumOne.exists_schwartz_lattice_sum_one Λ

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_partition_of_unity_lattice : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    ∃ h : SchwartzMap V ℂ, HasCompactSupport h ∧ ∀ x : V, HasSum (fun l : Λ => h (x + l)) 1 := by
  atlas_forward_decl GlobalTheory.exists_schwartz_hasCompactSupport_latticeTranslates_sum_one
end

section
section
open SchwartzMap

noncomputable section

namespace GlobalTheory.SchwartzTranslateSum

theorem summable_one_add_norm_inv_pow' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem summable_seminorm_mul_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall (0 : V)
  set N := Module.finrank ℤ Λ + 1 with hNdef
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hSdef
  set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h
    with hAdef
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  clear_value D A S R' N
  refine (hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)
  have hfun : (u l : V → ℂ) = fun y => h (y + l) * f y := funext (hu l)
  rw [hfun]
  have hsh : ContDiff ℝ n (fun y => h (y + (l : V))) :=
    ((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)
  have hsf : ContDiff ℝ n (f : V → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_add_right] at hleib
  by_cases hx : x + (l : V) ∈ tsupport h
  · have hxl : ‖x + (l : V)‖ ≤ R' := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (hR'def ▸ le_max_left _ _)
    have hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖) := by
      have : ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖ := by
        calc ‖(l : V)‖ = ‖(x + (l : V)) - x‖ := by simp
          _ ≤ ‖x + (l : V)‖ + ‖x‖ := norm_sub_le _ _
      have hn' : ‖l‖ = ‖(l : V)‖ := rfl
      nlinarith [norm_nonneg x]
    have hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N := by
      intro m hm
      have h1 := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m)
        le_rfl hm f x
      have h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S := by rw [hSdef]; exact h1
      have hpos : 0 < (1 + ‖l‖) ^ N := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ * (1 + ‖l‖) ^ N
          ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ * ((1 + R') * (1 + ‖x‖)) ^ N := by
            gcongr
            linarith [norm_nonneg x]
        _ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr
        _ = D := by rw [hDdef]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h (x + l)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h (x + l)‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h *
            (D * ((1 + ‖l‖)⁻¹) ^ N) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity))
              (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)
      _ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by
            rw [hAdef, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
  · have hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0 := fun i =>
      Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib
    have : ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0 :=
      le_antisymm hleib (norm_nonneg _)
    rw [this, mul_zero]
    exact mul_nonneg (mul_nonneg hA0 hD0) (by positivity)

end GlobalTheory.SchwartzTranslateSum
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_translates_cutoff_summable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h (x + l) * f x) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  atlas_forward_decl GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate
end

section
noncomputable section

namespace GlobalTheory.LatticeSchwartz

theorem summable_one_add_norm_inv_pow' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ}
    (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

theorem term_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h f : SchwartzMap V ℂ) (k N j m : ℕ) (x l : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ m f (x - l)‖ ≤
      (2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, m)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
      ((1 + ‖l‖)⁻¹) ^ N := by
  have hA := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, j)) le_rfl le_rfl h x
  have hB := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, m)) le_rfl le_rfl f (x - l)
  have hc : 1 + ‖l‖ ≤ (1 + ‖x‖) * (1 + ‖x - l‖) := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    nlinarith [norm_nonneg x, norm_nonneg (x - l)]
  have hc0 : 0 < 1 + ‖l‖ := by positivity
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  set P := ‖iteratedFDeriv ℝ j h x‖
  set Q := ‖iteratedFDeriv ℝ m f (x - l)‖
  have hP : 0 ≤ P := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖x‖ ^ k * P * Q * (1 + ‖l‖) ^ N
      ≤ (1 + ‖x‖) ^ k * P * Q * ((1 + ‖x‖) * (1 + ‖x - l‖)) ^ N := by gcongr
    _ = ((1 + ‖x‖) ^ (k + N) * P) * ((1 + ‖x - l‖) ^ N * Q) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

theorem summable_seminorm_mul_comp_sub : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  intro V _ _ _ Λ _ _ h f _ u hu k n
  set N := Module.finrank ℤ Λ + 1 with hN
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set D : ℕ → ℝ := fun j => (n.choose j : ℝ) *
      ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by
    have h1 : 0 ≤ (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h := apply_nonneg _ _
    have h2 : 0 ≤ (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := apply_nonneg _ _
    positivity
  set C := ∑ j ∈ Finset.range (n + 1), D j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hD0 j
  refine Summable.of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_) (hw.mul_left C)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) fun x => ?_
  have hul : (u l : V → ℂ) = fun y => h y * f (y - l) := funext (hu l)
  rw [hul]
  have hg : ContDiff ℝ n (fun y : V => f (y - (l : V))) :=
    (f.smooth n).comp (contDiff_id.sub contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (h.smooth n) hg x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_sub] at hL
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h y * f (y - l)) x‖
      ≤ ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖ := by
        gcongr
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by
        refine Finset.sum_le_sum fun j _ => ?_
        have ht := term_le h f k N j (n - j) x l
        have hch : (0 : ℝ) ≤ n.choose j := Nat.cast_nonneg _
        calc (n.choose j : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖)
            ≤ (n.choose j : ℝ) * ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup
                (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
              (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f) *
              ((1 + ‖(l : V)‖)⁻¹) ^ N) := mul_le_mul_of_nonneg_left ht hch
          _ = D j * ((1 + ‖(l : V)‖)⁻¹) ^ N := by rw [hD]; ring
    _ = C * ((1 + ‖l‖)⁻¹) ^ N := by rw [hC, Finset.sum_mul]; rfl

end GlobalTheory.LatticeSchwartz
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_shifted_cutoff_summable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h x * f (x - l)) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  first | exact @GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub | exact GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub | (intros; apply GlobalTheory.LatticeSchwartz.summable_seminorm_mul_comp_sub <;> assumption)
end

section
open Complex

namespace GlobalTheory.CharModGrowth

theorem norm_iteratedFDeriv_char_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ ≤ (|t| * ‖L‖) ^ n := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) := by
    fun_prop
  have e : (fun x : V => Complex.exp ((I * t) * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := n) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ n (fun y : ℝ => (1 : ℂ) * Complex.exp ((I * t) * (y : ℂ))) (L x)‖
          * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (|t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : (I * t) * ((L x : ℝ) : ℂ) = ((t * L x : ℝ) : ℂ) * I := by push_cast; ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
          Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
        simp [mul_pow]

theorem seminorm_char_mul_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) (f u : SchwartzMap V ℂ)
    (hu : ∀ x, u x = Complex.exp ((I * t) * (L x : ℂ)) * f x) {R : ℝ} (hR1 : 1 ≤ R)
    (hR : |t| * ‖L‖ ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n u ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) f)
        * R ^ n := by
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) f :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  have hR0 : 0 ≤ R := by linarith
  refine SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_
  have hu' : (⇑u) = fun x => Complex.exp ((I * t) * (L x : ℂ)) * f x := funext hu
  rw [hu']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L t).1 (f.smooth ⊤) x (n := n)
    (by exact_mod_cast le_top)
  calc _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖ :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖
            ≤ R ^ n :=
          (norm_iteratedFDeriv_char_le L t i x).trans
            ((pow_le_pow_left₀ (by positivity) hR i).trans (pow_le_pow_right₀ hR1 hi'))
        have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ SchwartzMap.seminorm ℂ k (n - i) f :=
          SchwartzMap.le_seminorm ℂ k (n - i) f x
        calc _ = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) *
              ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) x‖ := by ring
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)) h1
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

theorem seminorm_char_mul_polynomial_growth :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  intro V _ _ _ P h v hv k n
  let Q : V →L[ℝ] (V →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ
      LinearMap.flip P)
  have hQ : ∀ μ x, Q μ x = P x μ := fun μ x => rfl
  set A : ℝ := |2 * Real.pi| * ‖Q‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) h)
    * (1 + A) ^ n, fun μ => ?_⟩
  have hμ : 0 ≤ ‖μ‖ := norm_nonneg μ
  rw [mul_assoc, ← mul_pow]
  refine seminorm_char_mul_le (Q μ) (2 * Real.pi) h (v μ) (fun x => ?_) ?_ ?_ k n
  · rw [hv, hQ]; congr 2; push_cast; ring
  · nlinarith [mul_nonneg hA0 hμ]
  · calc |2 * Real.pi| * ‖Q μ‖ ≤ |2 * Real.pi| * (‖Q‖ * ‖μ‖) :=
          mul_le_mul_of_nonneg_left (Q.le_opNorm μ) (abs_nonneg _)
      _ = A * ‖μ‖ := by rw [hA]; ring
      _ ≤ _ := by nlinarith

end GlobalTheory.CharModGrowth
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulated_schwartz_seminorm_polynomial : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  first | exact @GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | exact GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | (intros; apply GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth <;> assumption)
end

section
section
open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap

namespace GlobalTheory

theorem schwartz_summable_norm_mul_one_add_pow {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (h : 𝓢(V, ℂ)) (N : ℕ) : Summable fun l : Λ => ‖h l‖ * (1 + ‖(l : V)‖) ^ N := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := GroundTheory.Global.exists_norm_le_inv_one_add_pow h (k + N)
  have hs : Summable fun l : Λ => C * ((1 + ‖l‖) ^ k)⁻¹ := by
    apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with l hl
    have hpos : 0 < ‖l‖ := norm_pos_iff.mpr hl
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  refine hs.of_nonneg_of_le (fun _ => by positivity) fun l => ?_
  have hp : 0 < 1 + ‖(l : V)‖ := by positivity
  calc ‖h l‖ * (1 + ‖(l : V)‖) ^ N
      ≤ C * ((1 + ‖(l : V)‖) ^ (k + N))⁻¹ * (1 + ‖(l : V)‖) ^ N := by
        gcongr
        exact hg _
    _ = C * ((1 + ‖(l : V)‖) ^ k)⁻¹ := by
        rw [pow_add]
        field_simp
    _ = C * ((1 + ‖l‖) ^ k)⁻¹ := rfl

theorem periodisation_hasSum_fourier_bilinForm {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (hP : P.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ) :
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let T : E ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let A₀ : V ≃ₗ[ℝ] E := (P.flip.toDual hP.flip) ≪≫ₗ T.toLinearEquiv.dualMap ≪≫ₗ
    (LinearMap.BilinForm.toDual (innerₗ E) GroundTheory.Global.innerₗ_nondegenerate).symm
  let A : V ≃L[ℝ] E := A₀.toContinuousLinearEquiv
  have hA : ∀ μ y, ⟪A μ, y⟫ = P (T y) μ := by
    intro μ y
    have h := LinearMap.BilinForm.toDual_def (B := innerₗ E) GroundTheory.Global.innerₗ_nondegenerate
      (m := A₀ μ) (n := y)
    have h2 : ⟪A μ, y⟫ = (innerₗ E) (A₀ μ) y := rfl
    rw [h2, ← h]
    simp only [A₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  let L : Submodule ℤ E := ZLattice.comap ℝ Λ T.toLinearMap
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ T.toLinearMap))
  haveI : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ T.toLinearMap))
  have hL : ∀ y, y ∈ L ↔ T y ∈ Λ := fun y => Iff.rfl
  let g : 𝓢(E, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f
  have hg : ∀ y, g y = f (T y) := fun y => rfl
  let Λ' : Submodule ℤ V := ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap
  haveI : DiscreteTopology Λ' :=
    inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap))
  have hmem : ∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) ↔ A μ ∈ GroundTheory.Global.dualLattice L := by
    intro μ
    rw [GroundTheory.Global.mem_dualLattice]
    constructor
    · intro h y hy
      rw [hA]
      exact h _ ((hL y).mp hy)
    · intro h l hl
      have := h (T.symm l) ((hL _).mpr (by simpa using hl))
      rwa [hA, T.apply_symm_apply] at this
  let h : 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A (𝓕 g)
  have hh : ∀ μ, h μ = 𝓕 (g : E → ℂ) (A μ) := fun μ => rfl
  refine ⟨fun μ => (ZLattice.covolume L)⁻¹ • h μ, fun N => ?_, fun x => ?_⟩
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ Λ' := Equiv.subtypeEquivRight hmem
    have hs := (e.summable_iff.mpr
      (schwartz_summable_norm_mul_one_add_pow Λ' h N)).mul_left ‖(ZLattice.covolume L)⁻¹‖
    refine hs.congr fun μ => ?_
    rw [norm_smul, mul_assoc]
    rfl
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ GroundTheory.Global.dualLattice L :=
      A.toEquiv.subtypeEquiv hmem
    let e' : L ≃ Λ := T.toEquiv.subtypeEquiv hL
    have hs := e.hasSum_iff.mpr
      (GroundTheory.Global.LatticePoisson.hasSum_smul_fourier (L := L) g (T.symm x))
    have hper : GroundTheory.Global.LatticePoisson.per L g (T.symm x) = ∑' l : Λ, f (x + l) := by
      rw [GroundTheory.Global.LatticePoisson.per, ← e'.tsum_eq]
      refine tsum_congr fun l => ?_
      rw [hg, map_add, T.apply_symm_apply]
      rfl
    rw [hper] at hs
    convert hs using 1
    funext μ
    have he : (e μ : E) = A μ := rfl
    simp only [Function.comp_apply, he, hA, T.apply_symm_apply, hh, Real.fourierChar_apply,
      smul_mul_assoc]
    congr 3
    push_cast
    ring

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_dual_fourier_expansion_schwartz : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ),
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  atlas_forward_decl GlobalTheory.periodisation_hasSum_fourier_bilinForm
end

section
namespace GlobalTheory.LatticeComb
open scoped SchwartzMap

theorem comb_unique : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (a : V) (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ l ∈ Λ, ∀ f f' : SchwartzMap V ℂ, (∀ x, f' x = f (x + l)) → T f' = T f) →
    (∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) → ∀ f f' : SchwartzMap V ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * f x) →
      T f' = Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap V ℂ, T f = c * ∑' l : Λ, f (a + l) := by
  intro V _ _ _ P hP Λ _ _ a T htr hmod
  obtain ⟨h, hhc, hh1⟩ := GlobalTheory.T.exists_schwartz_partition_of_unity_lattice Λ
  refine ⟨T h, fun f => ?_⟩
  have hth : ∀ l : Λ, (fun x => h (x + (l : V))).HasTemperateGrowth := fun l =>
    HasCompactSupport.hasTemperateGrowth (hhc.comp_homeomorph (Homeomorph.addRight (l : V)))
      ((h.smooth ⊤).comp (contDiff_id.add contDiff_const))
  have hh : (⇑h).HasTemperateGrowth := HasCompactSupport.hasTemperateGrowth hhc (h.smooth ⊤)
  let u : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (fun x => h (x + (l : V))) f
  have hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x := fun l x => by
    simp [u, SchwartzMap.smulLeftCLM_apply_apply (hth l)]
  obtain ⟨F1, hF1p, hF1T⟩ := GlobalTheory.T.summable_schwartz_series u (GlobalTheory.T.lattice_translates_cutoff_summable Λ h f hhc u hu)
  have hF1 : F1 = f := by
    ext x
    refine (hF1p x).unique ?_
    simpa [hu] using (hh1 x).mul_right (f x)
  let w : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (⇑h) (SchwartzMap.compSubConstCLM ℂ (l : V) f)
  have hw : ∀ (l : Λ) (x : V), w l x = h x * f (x - l) := fun l x => by
    simp [w, SchwartzMap.smulLeftCLM_apply_apply hh]
  have huw : ∀ l, T (u l) = T (w l) := fun l =>
    htr l l.2 (w l) (u l) (fun x => by rw [hu, hw]; simp)
  obtain ⟨G, hGp, hGT⟩ := GlobalTheory.T.summable_schwartz_series w (GlobalTheory.T.lattice_shifted_cutoff_summable Λ h f hhc w hw)
  have h1 : T f = T G := by
    have := hF1T T
    rw [hF1] at this
    simp_rw [huw] at this
    exact this.unique (hGT T)
  obtain ⟨c, hcs, hcP⟩ := GlobalTheory.T.lattice_dual_fourier_expansion_schwartz P hP Λ f
  have hch : ∀ μ : V, (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))).HasTemperateGrowth := by
    intro μ
    have e : (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) =
        fun x : V => Complex.exp ((Complex.I * ((2 * Real.pi : ℝ) : ℂ)) *
          ((LinearMap.toContinuousLinearMap (P.flip μ) x : ℝ) : ℂ)) := by
      funext x
      simp only [LinearMap.coe_toContinuousLinearMap']
      show _ = Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ) * ((P x μ : ℝ) : ℂ))
      push_cast; ring_nf
    rw [e]
    exact GlobalTheory.CharFormDeriv.hasTemperateGrowth_char (LinearMap.toContinuousLinearMap (P.flip μ)) (2 * Real.pi)
  let v0 : V → 𝓢(V, ℂ) := fun μ => SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) h
  have hv0 : ∀ μ x, v0 μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x := fun μ x => by
    simp [v0, SchwartzMap.smulLeftCLM_apply_apply (hch μ)]
  let v : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} → 𝓢(V, ℂ) := fun μ => c μ • v0 μ
  have hvs : ∀ k n : ℕ, Summable (fun μ => SchwartzMap.seminorm ℂ k n (v μ)) := by
    intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.T.modulated_schwartz_seminorm_polynomial P h v0 hv0 k n
    refine Summable.of_nonneg_of_le (fun μ => apply_nonneg _ _) (fun μ => ?_) ((hcs n).mul_left C)
    simp only [v, map_smul_eq_mul]
    calc ‖c μ‖ * SchwartzMap.seminorm ℂ k n (v0 μ) ≤ ‖c μ‖ * (C * (1 + ‖(μ : V)‖) ^ n) :=
          mul_le_mul_of_nonneg_left (hC μ) (norm_nonneg _)
      _ = C * (‖c μ‖ * (1 + ‖(μ : V)‖) ^ n) := by ring
  obtain ⟨G', hG'p, hG'T⟩ := GlobalTheory.T.summable_schwartz_series v hvs
  have hGG : G = G' := by
    ext x
    refine (hGp x).unique ?_
    have e1 : HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x)
        (h x * ∑' l : Λ, f (x + l)) := by
      have := (hcP x).mul_left (h x)
      have hfun : (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x) =
          fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => h x * (c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) := by
        funext μ
        simp only [v, SchwartzMap.smul_apply, hv0, smul_eq_mul]
        ring
      rw [hfun]; exact this
    have e2 : h x * ∑' l : Λ, f (x + l) = G' x := e1.unique (hG'p x)
    rw [← e2]
    have hsum : Summable (fun l : Λ => h x * f (x - l)) := by simpa [hw] using (hGp x).summable
    have e3 : ∑' l : Λ, f (x + l) = ∑' l : Λ, f (x - l) := by
      rw [← (Equiv.neg Λ).tsum_eq]
      simp [sub_eq_add_neg]
    rw [e3, ← tsum_mul_left]
    simpa [hw] using hsum.hasSum
  have hTv : ∀ μ, T (v μ) = c μ * Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T h := by
    intro μ
    simp only [v, map_smul, smul_eq_mul]
    rw [hmod μ μ.2 h (v0 μ) (hv0 μ)]
    ring
  have h2 := hG'T T
  simp_rw [hTv] at h2
  rw [h1, hGG, ← h2.tsum_eq, tsum_mul_right, (hcP a).tsum_eq, mul_comm]

end GlobalTheory.LatticeComb
end

section
section
open scoped Classical

namespace GlobalTheory.IntComb

noncomputable def dotForm (n : ℕ) : LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem dotForm_apply (n : ℕ) (x y : Fin n → ℝ) : dotForm n x y = ∑ i, x i * y i := rfl

theorem dotForm_nondegenerate (n : ℕ) : (dotForm n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have := hx (Pi.single i 1)
    simpa [dotForm_apply, Pi.single_apply] using this
  · intro y hy
    funext i
    have := hy (Pi.single i 1)
    simpa [dotForm_apply, Pi.single_apply] using this

abbrev intLat (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

theorem mem_intLat {n : ℕ} (x : Fin n → ℝ) :
    x ∈ intLat n ↔ ∃ k : Fin n → ℤ, x = fun i => (k i : ℝ) := by
  rw [intLat, (Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_intCast]
  constructor
  · intro h
    choose k hk using h
    exact ⟨k, funext fun i => (hk i).symm⟩
  · rintro ⟨k, rfl⟩ i
    exact ⟨k i, rfl⟩

noncomputable def intLatEquiv (n : ℕ) : (Fin n → ℤ) ≃ intLat n :=
  Equiv.ofBijective (fun k => ⟨fun i => (k i : ℝ), (mem_intLat _).2 ⟨k, rfl⟩⟩)
    ⟨fun k k' h => by
      funext i
      have : ((k i : ℤ) : ℝ) = (k' i : ℝ) := congrFun (congrArg Subtype.val h) i
      exact_mod_cast this,
     fun l => by
      obtain ⟨k, hk⟩ := (mem_intLat l.1).1 l.2
      exact ⟨k, Subtype.ext hk.symm⟩⟩

theorem dirac_comb_unique : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  intro n T htr hmod
  obtain ⟨c, hc⟩ := GlobalTheory.LatticeComb.comb_unique (Fin n → ℝ) (dotForm n) (dotForm_nondegenerate n)
    (intLat n) 0 T
    (fun l hl f f' hf => by
      obtain ⟨k, rfl⟩ := (mem_intLat l).1 hl
      exact htr k f f' hf)
    (fun μ hμ f f' hf => by
      have hi : ∀ i, ∃ z : ℤ, μ i = z := by
        intro i
        obtain ⟨z, hz⟩ := hμ (Pi.single i 1) ((mem_intLat _).2 ⟨Pi.single i 1, by
          funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]⟩)
        refine ⟨z, ?_⟩
        rw [← hz, dotForm_apply]
        simp [Pi.single_apply]
      choose m hm using hi
      have hμm : μ = fun i => (m i : ℝ) := funext hm
      subst hμm
      have h0 : dotForm n 0 (fun i => (m i : ℝ)) = 0 := by simp
      rw [h0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      refine hmod m f f' fun x => ?_
      rw [hf x, dotForm_apply]
      congr 3
      push_cast
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
  refine ⟨c, fun f => ?_⟩
  rw [hc f, ← (intLatEquiv n).tsum_eq]
  simp only [zero_add]
  rfl

end GlobalTheory.IntComb
end

open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_tempered_dist_poisson : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  atlas_forward_decl GlobalTheory.IntComb.dirac_comb_unique
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.LatUniq

theorem coe_mem_ints_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔ v.valuation F k ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem mem_scaledInt_iff {F : Type} [Field F] [NumberField F] {κ : Type} {a : F} (ha : a ≠ 0) (ξ : κ → F) :
    (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a ↔
      ∀ i, ∃ z : 𝓞 F, ξ i = a * (z : F) := by
  rw [GlobalTheory.EvAdm.mem_scaledInt]
  have key : ∀ (i : κ) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (v.adicCompletion F) a)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v =
        ((a⁻¹ * ξ i : F) : v.adicCompletion F) := by
    intro i v
    have h1 : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i) := rfl
    rw [h1, ← map_inv₀, ← map_mul]
    rfl
  constructor
  · intro h i
    have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1 := fun v => by
      have := h i v
      rw [key] at this
      exact (coe_mem_ints_iff v _).mp this
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
    refine ⟨z, ?_⟩
    have hz' : ((z : 𝓞 F) : F) = a⁻¹ * ξ i := hz
    rw [hz', ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · intro h i v
    obtain ⟨z, hz⟩ := h i
    rw [key, hz, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    exact (coe_mem_ints_iff v _).mpr (HeightOneSpectrum.valuation_le_one v z)

end GlobalTheory.LatUniq

namespace GlobalTheory.LatUniq

theorem transfer {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    (B : Module.Basis (Fin n) ℝ E) (T : SchwartzMap E ℂ →L[ℂ] ℂ)
    (h1 : ∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap E ℂ,
      (∀ x, f' x = f (x + ∑ l, (k l : ℝ) • B l)) → T f' = T f)
    (h2 : ∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap E ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ l, (m l : ℝ) * B.repr x l : ℝ) : ℂ)) * f x) →
        T f' = T f) :
    ∃ c : ℂ, ∀ f : SchwartzMap E ℂ, T f = c * ∑' k : Fin n → ℤ, f (∑ l, (k l : ℝ) • B l) := by
  let Φ : (Fin n → ℝ) ≃L[ℝ] E := B.equivFun.symm.toContinuousLinearEquiv
  have hΦ : ∀ t, Φ t = ∑ l, t l • B l := fun t => B.equivFun_symm_apply t
  have hΦs : ∀ y l, Φ.symm y l = B.repr y l := fun y l => rfl
  let C : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ.symm
  have hC : ∀ g y, C g y = g (Φ.symm y) := fun g y => rfl
  have t1 : ∀ k : Fin n → ℤ, ∀ g g' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, g' x = g (x + fun i => (k i : ℝ))) → (T.comp C) g' = (T.comp C) g := by
    intro k g g' hg
    show T (C g') = T (C g)
    apply h1 k
    intro y
    rw [hC, hC, hg]
    congr 1
    rw [ContinuousLinearEquiv.map_add, ← hΦ]
    simp
  have t2 : ∀ m : Fin n → ℤ, ∀ g g' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, g' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * g x) →
        (T.comp C) g' = (T.comp C) g := by
    intro m g g' hg
    show T (C g') = T (C g)
    apply h2 m
    intro y
    rw [hC, hC, hg]
    simp only [hΦs]
  obtain ⟨c, hc⟩ := GlobalTheory.T.periodic_tempered_dist_poisson n (T.comp C) t1 t2
  refine ⟨c, fun f => ?_⟩
  have hf : C (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ f) = f := by
    ext y; rw [hC]; simp
  have := hc (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ Φ f)
  rw [ContinuousLinearMap.comp_apply, hf] at this
  rw [this]
  congr 1
  refine tsum_congr fun k => ?_
  simp [hΦ]

end GlobalTheory.LatUniq

namespace GlobalTheory.LatUniq

variable {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ]

abbrev Idx (F : Type) [Field F] [NumberField F] := Σ _ : κ, Module.Free.ChooseBasisIndex ℤ (𝓞 F)

abbrev nn (F : Type) [Field F] [NumberField F] : ℕ := Fintype.card (Idx κ F)

def mulA (a : F) (ha : a ≠ 0) : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] mixedEmbedding.mixedSpace F where
  toFun x := mixedEmbedding F a * x
  invFun x := mixedEmbedding F a⁻¹ * x
  map_add' x y := mul_add _ x y
  map_smul' r x := mul_smul_comm r _ x
  left_inv x := by simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  right_inv x := by simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

def intBasis (F : Type) [Field F] [NumberField F] : Module.Basis (Fin (nn κ F)) ℤ (κ → 𝓞 F) :=
  (Pi.basis fun _ : κ => RingOfIntegers.basis F).reindex (Fintype.equivFin (Idx κ F))

def realBasis (a : F) (ha : a ≠ 0) : Module.Basis (Fin (nn κ F)) ℝ (κ → mixedEmbedding.mixedSpace F) :=
  (Pi.basis fun _ : κ => (mixedEmbedding.latticeBasis F).map (mulA a ha)).reindex (Fintype.equivFin (Idx κ F))

theorem realBasis_apply (a : F) (ha : a ≠ 0) (l : Fin (nn κ F)) (i : κ) :
    realBasis κ a ha l i = mixedEmbedding F (a * ((intBasis κ F l i : 𝓞 F) : F)) := by
  obtain ⟨p, rfl⟩ := (Fintype.equivFin (Idx κ F)).surjective l
  simp only [realBasis, intBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basis_apply,
    Module.Basis.map_apply]
  by_cases h : i = p.1
  · subst h
    simp [mulA, mixedEmbedding.latticeBasis_apply, integralBasis_apply]
  · simp [Pi.single_eq_of_ne h]

theorem sum_realBasis (a : F) (ha : a ≠ 0) (k : Fin (nn κ F) → ℤ) :
    ∑ l, (k l : ℝ) • realBasis κ a ha l =
      fun i => mixedEmbedding F (a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F)) := by
  funext i
  simp [Finset.sum_apply, realBasis_apply, Finset.mul_sum, mul_smul_comm, Int.cast_smul_eq_zsmul]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact mul_left_comm _ _ _

def dualVec (a : F) (m : Fin (nn κ F) → ℤ) : κ → F := fun i =>
  a⁻¹ * ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i, j⟩)) : ℚ) •
    (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j

theorem trace_dualVec (a : F) (ha : a ≠ 0) (m : Fin (nn κ F) → ℤ) (l : Fin (nn κ F)) :
    Algebra.trace ℚ F (∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i) = -(m l : ℚ) := by
  obtain ⟨⟨i₀, j₀⟩, rfl⟩ := (Fintype.equivFin (Idx κ F)).surjective l
  have hZ : ∀ i, intBasis κ F (Fintype.equivFin (Idx κ F) ⟨i₀, j₀⟩) i =
      Pi.single (M := fun _ : κ => 𝓞 F) i₀ (RingOfIntegers.basis F j₀) i := by
    intro i
    simp only [intBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basis_apply]
  rw [Finset.sum_eq_single i₀]
  · rw [hZ, Pi.single_eq_same]
    simp only [dualVec]
    have e1 : a * ((RingOfIntegers.basis F j₀ : 𝓞 F) : F) * (a⁻¹ * ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i₀, j⟩)) : ℚ) •
        (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j) =
        ∑ j, (-(m (Fintype.equivFin (Idx κ F) ⟨i₀, j⟩)) : ℚ) •
        ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F) j *
          ((RingOfIntegers.basis F j₀ : 𝓞 F) : F)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def]
      field_simp
    rw [e1, map_sum]
    have hd : ∀ j, Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F)
        (integralBasis F) j * ((RingOfIntegers.basis F j₀ : 𝓞 F) : F)) = if j₀ = j then 1 else 0 := by
      intro j
      have := (Algebra.traceForm ℚ F).apply_dualBasis_left (traceForm_nondegenerate ℚ F) (integralBasis F) j j₀
      rw [Algebra.traceForm_apply, integralBasis_apply] at this
      exact this
    simp only [map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro i _ hi
    rw [hZ, Pi.single_eq_of_ne hi]
    simp
  · simp

end GlobalTheory.LatUniq

namespace GlobalTheory.LatUniq

variable {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem char_identity (a : F) (ha : a ≠ 0) (m : Fin (nn κ F) → ℤ) (x : κ → mixedEmbedding.mixedSpace F) :
    ∑ l, (m l : ℝ) * (realBasis κ a ha).repr x l =
      -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (dualVec κ a m i)) := by
  have hl : ∀ l, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (∑ i, realBasis κ a ha l i * mixedEmbedding F (dualVec κ a m i)) = -(m l : ℝ) := by
    intro l
    have e : ∑ i, realBasis κ a ha l i * mixedEmbedding F (dualVec κ a m i) =
        mixedEmbedding F (∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i) := by
      simp only [realBasis_apply, map_sum, map_mul]
    rw [e, GlobalTheory.PsiNontriv.trace_mixedEmbedding, trace_dualVec κ a ha m l]
    push_cast
    rfl
  conv_rhs => rw [← (realBasis κ a ha).sum_repr x]
  simp only [Finset.sum_apply, Pi.smul_apply, Finset.sum_mul, smul_mul_assoc]
  rw [Finset.sum_comm, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.smul_sum, map_smul, smul_eq_mul, hl]
  ring

theorem main_lat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i))) → T f' = T f) →
    (∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
        T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      T f = c * ∑' ξ : κ → F, {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun ξ => f (fun i => mixedEmbedding F (ξ i))) ξ := by
  intro F _ _ κ _ a ha T hT hC
  have h1 : ∀ k : Fin (nn κ F) → ℤ, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = f (x + ∑ l, (k l : ℝ) • realBasis κ a ha l)) → T f' = T f := by
    intro k f f' hf
    refine hT (fun i => a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F))
      ((mem_scaledInt_iff ha _).mpr fun i => ⟨_, rfl⟩) f f' fun x => ?_
    rw [hf, sum_realBasis]
  have h2 : ∀ m : Fin (nn κ F) → ℤ, ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I *
        ((∑ l, (m l : ℝ) * (realBasis κ a ha).repr x l : ℝ) : ℂ)) * f x) → T f' = T f := by
    intro m f f' hf
    refine hC (dualVec κ a m) ?_ f f' fun x => ?_
    · intro ξ hξ
      choose z hz using (mem_scaledInt_iff ha ξ).mp hξ
      refine ⟨∑ l, (intBasis κ F).repr z l * (-(m l)), ?_⟩
      have hzs := (intBasis κ F).sum_repr z
      have hξ' : ξ = fun i => a * (((∑ l, (intBasis κ F).repr z l • intBasis κ F l) i : 𝓞 F) : F) := by
        funext i; rw [hzs, hz i]
      rw [hξ']
      have e : ∑ i, a * (((∑ l, (intBasis κ F).repr z l • intBasis κ F l) i : 𝓞 F) : F) * dualVec κ a m i =
          ∑ l, (intBasis κ F).repr z l • ∑ i, (a * ((intBasis κ F l i : 𝓞 F) : F)) * dualVec κ a m i := by
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.mul_sum, Finset.sum_mul,
          Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, smul_mul_assoc]
      rw [e, map_sum]
      push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_zsmul, trace_dualVec κ a ha m l, zsmul_eq_mul]
    · rw [hf, char_identity]
      congr 1
      push_cast
      ring_nf
  obtain ⟨c, hc⟩ := transfer (realBasis κ a ha) T h1 h2
  refine ⟨c, fun f => ?_⟩
  rw [hc f]
  congr 1
  rw [← tsum_subtype]
  let S : Set (κ → F) := {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}
  let θ : (Fin (nn κ F) → ℤ) → S := fun k =>
    ⟨fun i => a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F), (mem_scaledInt_iff ha _).mpr fun i => ⟨_, rfl⟩⟩
  have hsum : ∀ k : Fin (nn κ F) → ℤ, ∑ l, k l • intBasis κ F l = (intBasis κ F).equivFun.symm k := fun k =>
    ((intBasis κ F).equivFun_symm_apply k).symm
  have hθ : Function.Bijective θ := by
    constructor
    · intro k k' hkk
      have h0 : ∀ i, a * (((∑ l, k l • intBasis κ F l) i : 𝓞 F) : F) =
          a * (((∑ l, k' l • intBasis κ F l) i : 𝓞 F) : F) := fun i => congrFun (congrArg Subtype.val hkk) i
      have h3 : ∑ l, k l • intBasis κ F l = ∑ l, k' l • intBasis κ F l := by
        funext i
        exact RingOfIntegers.coe_injective (mul_left_cancel₀ ha (h0 i))
      rw [hsum, hsum] at h3
      exact (intBasis κ F).equivFun.symm.injective h3
    · rintro ⟨ξ, hξ⟩
      choose z hz using (mem_scaledInt_iff ha ξ).mp hξ
      refine ⟨(intBasis κ F).equivFun z, Subtype.ext ?_⟩
      funext i
      show a * (((∑ l, _ • intBasis κ F l) i : 𝓞 F) : F) = ξ i
      rw [hsum, LinearEquiv.symm_apply_apply, hz i]
  rw [← (Equiv.ofBijective θ hθ).tsum_eq]
  refine tsum_congr fun k => ?_
  rw [sum_realBasis]
  rfl

end GlobalTheory.LatUniq
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_lattice_translation_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
    (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i))) → T f' = T f) →
    (∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
      ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
        T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      T f = c * ∑' ξ : κ → F, {ξ : κ → F | (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun ξ => f (fun i => mixedEmbedding F (ξ i))) ξ := by
  atlas_forward_decl GlobalTheory.LatUniq.main_lat
end
