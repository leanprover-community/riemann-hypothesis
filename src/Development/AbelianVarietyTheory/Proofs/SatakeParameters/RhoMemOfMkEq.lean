import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalSubgroupContainingHyperspecialEqTopUnramif
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacua
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexLeOfIntegralKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittTheoremModUniformizerPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint

section
section
open Submodule MulAction

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

def WA (V : ι → Submodule ℂ M) (A : Set ι) : Submodule ℂ M := ⨆ (j) (_ : j ∈ A), V j

theorem WA_mono (V : ι → Submodule ℂ M) {A B : Set ι} (h : A ⊆ B) : WA V A ≤ WA V B :=
  biSup_mono fun _ hj => h hj

theorem le_WA (V : ι → Submodule ℂ M) {A : Set ι} {j : ι} (hj : j ∈ A) : V j ≤ WA V A :=
  le_iSup₂_of_le j hj le_rfl

theorem WA_union (V : ι → Submodule ℂ M) (A B : Set ι) : WA V (A ∪ B) = WA V A ⊔ WA V B :=
  iSup_union

theorem iSup_orbit (V : ι → Submodule ℂ M) (i : ι) :
    (⨆ g : G, V (g • i)) = WA V (orbit G i) := by
  apply le_antisymm
  · exact iSup_le fun g => le_WA V (mem_orbit i g)
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨g, rfl⟩ := hj
    exact le_iSup (fun g : G => V (g • i)) g

theorem orbit_stable (i : ι) (g : G) {j : ι} (hj : j ∈ orbit G i) : g • j ∈ orbit G i := by
  obtain ⟨h, rfl⟩ := hj
  exact ⟨g * h, mul_smul g h i⟩

theorem map_WA_le (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (g : G) {x : M} (hx : x ∈ WA V A) :
    π g x ∈ WA V A := by
  have : (WA V A).map (π g) ≤ WA V A := by
    unfold WA
    rw [Submodule.map_iSup]
    refine iSup_le fun j => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hj => (hπ g j).trans (le_WA V (hA g j hj))
  exact this (Submodule.mem_map_of_mem hx)

theorem fixed_part (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A B : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (hB : ∀ (g : G), ∀ j ∈ B, g • j ∈ B)
    (hAB : Disjoint A B) {a b : M} (ha : a ∈ WA V A) (hb : b ∈ WA V B)
    (hfix : ∀ g, π g (a + b) = a + b) : ∀ g, π g a = a := by
  intro g
  have h1 : π g a - a ∈ WA V A := sub_mem (map_WA_le π V hπ hA g ha) ha
  have h2 : π g a - a ∈ WA V B := by
    have e : π g a - a = b - π g b := by
      rw [sub_eq_sub_iff_add_eq_add, ← map_add, hfix g, add_comm]
    rw [e]
    exact sub_mem hb (map_WA_le π V hπ hB g hb)
  have hd : Disjoint (WA V A) (WA V B) := hV.disjoint_biSup_biSup hAB
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ h1 h2)

theorem exists_comp (V : ι → Submodule ℂ M) (hV : iSupIndep V) (htop : (⨆ i, V i) = ⊤) :
    ∃ c : ι → M →ₗ[ℂ] M, (∀ i w, c i w ∈ V i) ∧ (∀ i v, v ∈ V i → c i v = v) ∧
      (∀ i j v, i ≠ j → v ∈ V j → c i v = 0) ∧ (∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w) := by
  classical
  letI := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV htop).chooseDecomposition
  refine ⟨fun i => (V i).subtype ∘ₗ (DirectSum.component ℂ ι (fun i => ↥(V i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv V).toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro i w; simp
  · intro i v hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_same V hv
  · intro i j v hij hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_ne V hv hij.symm
  · intro w
    refine ⟨(DirectSum.decompose V w).support, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact (DirectSum.sum_support_decompose V w).symm

end GlobalTheory.GradedFixed

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

section comp

variable (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (c : ι → M →ₗ[ℂ] M)
  (hc1 : ∀ i w, c i w ∈ V i) (hc2 : ∀ i v, v ∈ V i → c i v = v)
  (hc3 : ∀ i j v, i ≠ j → v ∈ V j → c i v = 0) (hc4 : ∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w)
include hc1 hc2 hc3 hc4

theorem comp_equivariant (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (g : G) (i : ι) (w : M) : c (g • i) (π g w) = π g (c i w) := by
  obtain ⟨F, hF⟩ := hc4 w
  rw [hF, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem : π g (c j w) ∈ V (g • j) := hπ g j (Submodule.mem_map_of_mem (hc1 j w))
  by_cases hij : j = i
  · subst hij
    rw [hc2 _ _ hmem, hc2 _ _ (hc1 j w)]
  · rw [hc3 _ _ _ (fun h => hij (smul_left_cancel g h).symm) hmem, hc3 _ _ _ (Ne.symm hij) (hc1 j w),
      map_zero]

omit hc1 hc2 hc4 in
theorem comp_outside {A : Set ι} {x : M} (hx : x ∈ WA V A) {l : ι} (hl : l ∉ A) : c l x = 0 := by
  have : WA V A ≤ LinearMap.ker (c l) :=
    iSup₂_le fun j hj v hv => LinearMap.mem_ker.mpr (hc3 l j v (fun h => hl (h ▸ hj)) hv)
  exact LinearMap.mem_ker.mp (this hx)

omit hc1 hc2 hc3 in
theorem eq_zero_of_comp {x : M} (h : ∀ l, c l x = 0) : x = 0 := by
  obtain ⟨F, hF⟩ := hc4 x
  rw [hF]
  exact Finset.sum_eq_zero fun l _ => h l

omit hc2 hc4 in
theorem mem_WA_of_sum {A : Set ι} {F : Finset ι} (hF : ∀ j ∈ F, j ∈ A) (w : M)
    (hw : w = ∑ i ∈ F, c i w) : w ∈ WA V A := by
  rw [hw]
  exact Submodule.sum_mem _ fun j hj => le_WA V (hF j hj) (hc1 j w)

theorem mem_span_of_fixed (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (hline : ∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) (i : ι) {x y : M}
    (hx : ∀ g, π g x = x) (hy : ∀ g, π g y = y) (hxO : x ∈ WA V (orbit G i))
    (hyO : y ∈ WA V (orbit G i)) (hy0 : y ≠ 0) : x ∈ Submodule.span ℂ {y} := by
  obtain ⟨F, hF⟩ := hc4 y
  obtain ⟨k, -, hk⟩ : ∃ k ∈ F, c k y ≠ 0 := by
    by_contra! h
    exact hy0 (by rw [hF]; exact Finset.sum_eq_zero h)
  have hkO : k ∈ orbit G i := by
    by_contra hkO
    exact hk (comp_outside V c hc3 hyO hkO)
  obtain ⟨v, hv⟩ := hline k
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hv (hc1 k y))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv (hc1 k x))
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hk (by rw [← hb, zero_smul])
  set z := x - (a / b) • y with hz
  have hzk : c k z = 0 := by
    rw [hz, map_sub, map_smul, ← ha, ← hb, smul_smul, div_mul_cancel₀ a hb0, sub_self]
  have hzfix : ∀ g, π g z = z := fun g => by rw [hz, map_sub, map_smul, hx, hy]
  have hzO : z ∈ WA V (orbit G i) := sub_mem hxO (Submodule.smul_mem _ _ hyO)
  have hz0 : z = 0 := by
    refine eq_zero_of_comp c hc4 fun l => ?_
    by_cases hl : l ∈ orbit G i
    · obtain ⟨g0, rfl⟩ := hkO
      obtain ⟨g1, rfl⟩ := hl
      have e : g1 • i = (g1 * g0⁻¹) • (g0 • i) := by rw [smul_smul, inv_mul_cancel_right]
      simp only at hzk ⊢
      rw [e, ← hzfix (g1 * g0⁻¹), comp_equivariant π V c hc1 hc2 hc3 hc4 hπ, hzk, map_zero]
    · exact comp_outside V c hc3 hzO hl
  rw [hz, sub_eq_zero] at hz0
  rw [hz0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)

end comp

end GlobalTheory.GradedFixed

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem mem_of_orbits (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) (S : Submodule ℂ M) (F : Finset ι) :
    (∀ i ∈ F, ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
    ∀ u, (∀ g, π g u = u) → u ∈ WA V (⋃ i ∈ F, orbit G i) → u ∈ S := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _ u _ hu
    have : u = 0 := by simpa [WA] using hu
    rw [this]; exact zero_mem S
  | insert i F hi ih =>
    intro hT u hu huF
    have hset : (⋃ j ∈ insert i F, orbit G j) = orbit G i ∪ ((⋃ j ∈ F, orbit G j) \ orbit G i) := by
      rw [Finset.set_biUnion_insert, Set.union_diff_self]
    rw [hset, WA_union, Submodule.mem_sup] at huF
    obtain ⟨a, ha, b, hb, rfl⟩ := huF
    have hA : ∀ (g : G), ∀ j ∈ orbit G i, g • j ∈ orbit G i := fun g j hj => orbit_stable i g hj
    have hU : ∀ (g : G), ∀ j ∈ (⋃ k ∈ F, orbit G k), g • j ∈ (⋃ k ∈ F, orbit G k) := by
      intro g j hj
      obtain ⟨k, hk, hjk⟩ := Set.mem_iUnion₂.mp hj
      exact Set.mem_iUnion₂.mpr ⟨k, hk, orbit_stable k g hjk⟩
    have hB : ∀ (g : G), ∀ j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i),
        g • j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i) := by
      intro g j hj
      exact ⟨hU g j hj.1, fun h => hj.2 (by simpa using orbit_stable i g⁻¹ h)⟩
    have hAB : Disjoint (orbit G i) ((⋃ k ∈ F, orbit G k) \ orbit G i) := Set.disjoint_sdiff_right
    have hafix := fixed_part π V hV hπ hA hB hAB ha hb hu
    have hbfix : ∀ g, π g b = b :=
      fixed_part π V hV hπ hB hA hAB.symm hb ha (fun g => by rw [add_comm]; exact hu g)
    exact add_mem (hT i (Finset.mem_insert_self i F) a hafix ha)
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)) b hbfix (WA_mono V Set.diff_subset hb))

end GlobalTheory.GradedFixed

namespace GlobalTheory

open GlobalTheory.GradedFixed in

theorem fixed_mem_of_orbit_height : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  intro G ι M _ _ _ _ π V hV htop hline hπ μ hμ S hS hstep
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_comp V hV htop
  have hsum : ∀ (p : ι → Prop) (u : M), (∀ l, ¬ p l → c l u = 0) →
      (∀ i, p i → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
      (∀ g, π g u = u) → u ∈ S := by
    classical
    intro p u hp hgood hu
    obtain ⟨F, hF⟩ := hc4 u
    have hF' : u = ∑ j ∈ F.filter p, c j u := by
      rw [Finset.sum_filter_of_ne (fun j _ h => by_contra fun hpj => h (hp j hpj))]
      exact hF
    refine mem_of_orbits π V hV hπ S (F.filter p)
      (fun j hj => hgood j (Finset.mem_filter.mp hj).2) u hu ?_
    exact mem_WA_of_sum V c hc1 hc3
      (fun j hj => Set.mem_iUnion₂.mpr ⟨j, hj, (mem_orbit_self j : j ∈ orbit G j)⟩) u hF'
  have key : ∀ m i, μ i = m → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi x hx hxO
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem S
    obtain ⟨v, hvS, u, hu, hvu, hvu0⟩ := hstep i ⟨x, hx0, hx, by rw [iSup_orbit]; exact hxO⟩
    rw [iSup_orbit] at hvu
    have huW : u ∈ WA V {j | μ j < μ i} := hu
    have hsub : {j | μ j < μ i} ⊆ (orbit G i)ᶜ := by
      intro j hj hjO
      obtain ⟨g, rfl⟩ := hjO
      simp [hμ] at hj
    have hcompl : ∀ (g : G), ∀ j ∈ (orbit G i)ᶜ, g • j ∈ (orbit G i)ᶜ :=
      fun g j hj hgj => hj (by simpa using orbit_stable i g⁻¹ hgj)
    have hfa : ∀ g, π g (v - u) = v - u :=
      fixed_part π V hV hπ (fun g j hj => orbit_stable i g hj) hcompl disjoint_compl_right hvu
        (WA_mono V hsub huW) (fun g => by rw [sub_add_cancel]; exact hS v hvS g)
    have hufix : ∀ g, π g u = u := fun g => by
      have h1 := hfa g
      rw [map_sub, hS v hvS g] at h1
      exact sub_right_injective h1
    have huS : u ∈ S := hsum (fun j => μ j < μ i) u (fun l hl => comp_outside V c hc3 huW hl)
      (fun j hj => ih (μ j) (hi ▸ hj) j rfl) hufix
    have hvuS : v - u ∈ S := sub_mem hvS huS
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (mem_span_of_fixed π V c hc1 hc2 hc3 hc4 hπ hline i hx hfa hxO hvu hvu0)
    rw [← hr]
    exact S.smul_mem r hvuS
  intro w hw
  exact hsum (fun _ => True) w (fun l hl => absurd trivial hl) (fun i _ => key (μ i) i rfl) hw

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_mem_of_orbit_height_separation : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  atlas_forward_decl GlobalTheory.fixed_mem_of_orbit_height
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_invariance | exact GlobalTheory.Hk3.HoweDuality.latIdx_invariance | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_invariance <;> assumption)
end

section
section
open Matrix

namespace GlobalTheory.Hk3

theorem locVac_mem_span_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac hspan w hw
  classical
  have hind := locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) s = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x s := by
    intro x u hu
    have h1 : ρ x s = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) s := by
      have := congrArg (fun f => f s) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x s) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x s := by
    intro x u hu
    have := congrArg (fun f => f s) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  set Λ := HoweDuality.intMat L n' n with hΛdef
  set V : Matrix (Fin n') (Fin n) L ⧸ Λ → Submodule ℂ M := fun c => Submodule.span ℂ {ρ c.out s} with hVdef
  have hVind : iSupIndep V := by
    refine hind.mono fun c => Submodule.span_le.mpr ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨c.out, QuotientAddGroup.out_eq' c, rfl⟩
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := by
    intro x
    have hm : -(QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq'])
    have := hshift (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out _ hm
    rw [add_neg_cancel_left] at this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hwV : w ∈ ⨆ c, V c := by
    have hle : Submodule.span ℂ (Set.range fun x => ρ x s) ≤ ⨆ c, V c :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Submodule.mem_iSup_of_mem _ (hmemV x))
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨f, hf, hfw⟩ := (Submodule.mem_iSup_iff_exists_finsupp V w).mp hwV
  set χ : Matrix (Fin n') (Fin n) L ⧸ Λ → Matrix (Fin n') (Fin n) L → ℂ :=
    fun c u => ψ (locH σ δ JS JT u c.out + σ (locH σ δ JS JT u c.out)) with hχ
  have heigV : ∀ c, ∀ u ∈ intMatSub (L := L) n n', ∀ v ∈ V c, ρ u v = χ c u • v := by
    intro c u hu v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, heig _ u hu, smul_comm]
  have hzero : ∀ c, c ≠ 0 → f c = 0 := by
    intro c hc
    obtain ⟨u, hu, hχu⟩ : ∃ u ∈ intMatSub (L := L) n n', χ c u ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hint := intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne c.out hcon
      apply hc
      rw [hΛ] at hint
      rw [← QuotientAddGroup.out_eq' c, QuotientAddGroup.eq_zero_iff]
      exact hint
    have hsum : (f.support.sum fun d => (χ d u - 1) • f d) = 0 := by
      have e1 : ρ u w = f.support.sum fun d => χ d u • f d := by
        rw [← hfw, Finsupp.sum, map_sum]
        exact Finset.sum_congr rfl fun d _ => heigV d u hu _ (hf d)
      have e2 : w = f.support.sum fun d => f d := by rw [← hfw, Finsupp.sum]
      simp only [sub_smul, one_smul, Finset.sum_sub_distrib, ← e1, ← e2, hw u hu, sub_self]
    by_cases hcs : c ∈ f.support
    · rw [← Finset.add_sum_erase _ _ hcs, add_eq_zero_iff_eq_neg] at hsum
      have hmem1 : (χ c u - 1) • f c ∈ V c := Submodule.smul_mem _ _ (hf c)
      have hmem2 : (χ c u - 1) • f c ∈ ⨆ (j) (_ : j ≠ c), V j := by
        rw [hsum]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => ?_)
        have hdc : d ≠ c := Finset.ne_of_mem_erase hd
        exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hdc (Submodule.smul_mem _ _ (hf d)))
      have hz : (χ c u - 1) • f c = 0 := by
        have := (iSupIndep_def.mp hVind c)
        rw [Submodule.disjoint_def] at this
        exact this _ hmem1 hmem2
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)
    · exact Finsupp.notMem_support_iff.mp hcs
  have hw0 : w = f 0 := by
    rw [← hfw, Finsupp.sum, Finset.sum_eq_single (0 : Matrix (Fin n') (Fin n) L ⧸ Λ)]
    · intro d _ hd; exact hzero d hd
    · intro h0; exact Finsupp.notMem_support_iff.mp h0
  have hout : ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s = s := by
    apply hvac
    have : (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out ∈ Λ := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
    exact this
  have := hf 0
  change f 0 ∈ Submodule.span ℂ {ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s} at this
  rw [hout] at this
  rw [hw0]; exact this

end GlobalTheory.Hk3
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLatticeVacuum_mem_span_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  atlas_forward_decl GlobalTheory.Hk3.locVac_mem_span_vac
end

section
section
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem mem_GLint_of_entries' {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

def cTGL {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (a : GL (Fin n) L) : GL (Fin n) L :=
  ⟨Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L), Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one],
    by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]⟩

theorem selfDual_eq_unitary_mul_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  intro L _ _ _ ϖ σ q n JS hU _hq hJS hJh a ha
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have cTcT : ∀ M : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    intro M; ext i j; simp [Formalism.UG.cT, hσ]
  have hJc : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j; simp [Formalism.UG.cT, hJh]
  set G : GL (Fin n) L := cTGL σ a * JS * a with hGdef
  have hGv : (G : Matrix (Fin n) (Fin n) L) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := rfl
  have hGi : ((G⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hGdef, _root_.mul_inv_rev, _root_.mul_inv_rev, ← _root_.mul_assoc]; rfl
  have hGint : G ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) :=
    mem_GLint_of_entries' _ G (fun i j => by rw [hGv]; exact ha.1 i j) (fun i j => by rw [hGi]; exact ha.2 i j)
  have hGc : Formalism.UG.cT σ (G : Matrix (Fin n) (Fin n) L) = G := by
    rw [hGv, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTcT, hJc, Matrix.mul_assoc]
  have hGh : ∀ i j, σ ((G : Matrix (Fin n) (Fin n) L) i j) = (G : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    have := congrFun (congrFun hGc j) i
    simpa [Formalism.UG.cT] using this
  obtain ⟨P, hP, eP⟩ := GlobalTheory.NormalHyp.frame hU hGint hGh
  obtain ⟨Q, hQ, eQ⟩ := GlobalTheory.NormalHyp.frame hU hJS hJh
  have hU' : a * P * Q⁻¹ ∈ Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
      ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = JS
    have e1 : Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
    have e2 : (Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv Q
    rw [hGv] at eP
    calc Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
          ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
        = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (P : Matrix (Fin n) (Fin n) L) * (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) *
              (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) * (P : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (Q : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by rw [eP, eQ]
      _ = (Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L)) *
            (JS : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
          simp only [Matrix.mul_assoc]
      _ = JS := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨a * P * Q⁻¹, hU'⟩, Q * P⁻¹, mul_mem hQ (inv_mem hP), ?_⟩
  show a = a * P * Q⁻¹ * (Q * P⁻¹)
  group

end GlobalTheory.Hk3.HoweG

end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_eq_unitary_mul_integralGL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  atlas_forward_decl GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int
end

section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q a b : ℕ) (x y : Matrix (Fin a) (Fin b) L),
    Formalism.UG.IsUnramInv ϖ σ q →
    (∀ u : Fin b → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (Matrix.mulVec x u) i ∈ Formalism.UG.intL L) → ∀ i, (Matrix.mulVec y u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y ≤ GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | exact GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker <;> assumption)
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt.ElemDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {m k : ℕ} {A : Matrix (Fin m) (Fin k) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    {c : Fin k → L} (hc : ∀ j, c j ∈ Formalism.UG.intL L) : ∀ i, (A *ᵥ c) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hc j)

theorem diag_mulVec_of_lt {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (j : Fin n) (hj : (j : ℕ) < n') :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) ⟨j, hj⟩ =
      (if 0 < a ⟨j, hj⟩ then ϖ⁻¹ ^ a ⟨j, hj⟩ else 0) * c j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : ¬ ((j : ℕ) = (b : ℕ)) := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

theorem diag_mulVec_of_ge {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (i : Fin n') (hi : ¬ (i : ℕ) < n) :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) i = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro b _
  have : ¬ ((i : ℕ) = (b : ℕ)) := fun h => hi (h ▸ b.isLt)
  simp [this]

end GlobalTheory.Hk3.IntWitt.ElemDiv

end

open GlobalTheory.Hk3.IntWitt.ElemDiv in

theorem GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ V : GL (Fin n) L, V ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧ ∃ a : Fin n → ℕ,
      ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
        ((∀ i, (x *ᵥ ((V : Matrix (Fin n) (Fin n) L) *ᵥ c)) i ∈ Formalism.UG.intL L) ↔
          ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
  intro L _ _ ϖ hϖ n n' x
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.Hk3.smith_int_approx L ϖ hϖ n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  set O := Formalism.UG.intL L with hOdef
  let QO : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q i j, hQ i j⟩
  let QO' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q' i j, hQ' i j⟩
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) L) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hm1 : O.subtype.mapMatrix QO = Q := by ext i j; rfl
  have hm2 : O.subtype.mapMatrix QO' = Q' := by ext i j; rfl
  have e1 : QO * QO' = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQQ'])
  have e2 : QO' * QO = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQ'Q])
  let U : GL (Fin n) O := ⟨QO, QO', e1, e2⟩
  let V : GL (Fin n) L := ⟨Q, Q', hQQ', hQ'Q⟩
  refine ⟨V, ⟨U, Units.ext hm1⟩, fun j => if h : (j : ℕ) < n' then a ⟨j, h⟩ else 0, ?_⟩
  intro c hc
  set Dm : Matrix (Fin n') (Fin n) L :=
    Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDm
  have hPw : P *ᵥ (x *ᵥ (Q *ᵥ c)) = Dm *ᵥ c + (P * x * Q - Dm) *ᵥ c := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hEc : ∀ i, ((P * x * Q - Dm) *ᵥ c) i ∈ O := mulVec_int hE hc
  show (∀ i, (x *ᵥ (Q *ᵥ c)) i ∈ O) ↔ _
  constructor
  · intro hw j
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      have h1 := mulVec_int hP hw i
      rw [hPw, Pi.add_apply] at h1
      have := Subring.sub_mem _ h1 (hEc i)
      rwa [add_sub_cancel_right] at this
    by_cases hj : (j : ℕ) < n'
    · simp only [dif_pos hj]
      have h2 := hDc ⟨j, hj⟩
      rw [hDm, diag_mulVec_of_lt ϖ a c j hj] at h2
      split_ifs at h2 with ha
      · refine ⟨ϖ⁻¹ ^ a ⟨j, hj⟩ * c j, h2, ?_⟩
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow, one_mul]
      · have : a ⟨j, hj⟩ = 0 := by omega
        rw [this]; exact dvdPow_zero_iff.mpr (hc j)
    · simp only [dif_neg hj]; exact dvdPow_zero_iff.mpr (hc j)
  · intro hd
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      by_cases hi : (i : ℕ) < n
      · have hij : i = ⟨((⟨i, hi⟩ : Fin n) : ℕ), i.isLt⟩ := Fin.ext rfl
        rw [hij, hDm, diag_mulVec_of_lt ϖ a c ⟨i, hi⟩ i.isLt]
        split_ifs with ha
        · have h3 := hd ⟨i, hi⟩
          simp only [dif_pos i.isLt] at h3
          obtain ⟨b, hb, hcb⟩ := h3
          rw [hcb, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, one_mul]; exact hb
        · rw [zero_mul]; exact Subring.zero_mem _
      · rw [hDm, diag_mulVec_of_ge ϖ a c i hi]; exact Subring.zero_mem _
    have hPwi : ∀ i, (P *ᵥ (x *ᵥ (Q *ᵥ c))) i ∈ O := by
      intro i; rw [hPw, Pi.add_apply]; exact Subring.add_mem _ (hDc i) (hEc i)
    intro i
    have key : ∀ w : Fin n' → L, w = P' *ᵥ (P *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
    rw [key (x *ᵥ (Q *ᵥ c))]; exact mulVec_int hP' hPwi i
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elementaryDivisors_integral_preimage_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ V : GL (Fin n) L, V ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧ ∃ a : Fin n → ℕ,
      ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
        ((∀ i, (x *ᵥ ((V : Matrix (Fin n) (Fin n) L) *ᵥ c)) i ∈ Formalism.UG.intL L) ↔
          ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
  atlas_forward_decl GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

theorem ker_le_of_latIdx_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q hU n n' x y hN hidx u hu hyu
  classical
  have hfin := finite_range_latIdx hU x
  set Sx := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSx
  set Sy := Set.range fun u : intVec L n =>
      (QuotientAddGroup.mk (y *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') with hSy
  let h : (Fin n' → L) ⧸ intVec L n' → (Fin n' → L) ⧸ intVec L n' := fun c =>
    if hc : ∃ u : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') = c
    then QuotientAddGroup.mk (y *ᵥ (hc.choose : Fin n → L)) else 0
  have key : ∀ w : intVec L n, h (QuotientAddGroup.mk (x *ᵥ (w : Fin n → L))) =
      (QuotientAddGroup.mk (y *ᵥ (w : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') := by
    intro w
    have hc : ∃ u' : intVec L n, (QuotientAddGroup.mk (x *ᵥ (u' : Fin n → L)) : (Fin n' → L) ⧸ intVec L n') =
        QuotientAddGroup.mk (x *ᵥ (w : Fin n → L)) := ⟨w, rfl⟩
    simp only [h, dif_pos hc]
    have he := hc.choose_spec
    set u' := hc.choose
    rw [QuotientAddGroup.eq] at he
    rw [QuotientAddGroup.eq]
    have hd := hN ((w : Fin n → L) - (u' : Fin n → L)) (fun i => Subring.sub_mem _ (w.2 i) (u'.2 i))
      (fun i => by
        have := he i
        rw [Matrix.mulVec_sub]
        simpa [neg_add_eq_sub] using this)
    intro i
    have := hd i
    rw [Matrix.mulVec_sub] at this
    simpa [neg_add_eq_sub] using this
  have himg : h '' Sx = Sy := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (key w).symm⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨_, ⟨w, rfl⟩, key w⟩
  have hcard : (h '' Sx).ncard = Sx.ncard := by
    rw [himg]
    unfold latIdx at hidx
    rw [← hSx, ← hSy, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hidx
    exact hidx
  have hinj : Set.InjOn h Sx := (Set.ncard_image_iff hfin).1 hcard
  let u0 : intVec L n := ⟨u, hu⟩
  have h0 : h (QuotientAddGroup.mk (x *ᵥ ((u0 : intVec L n) : Fin n → L))) = h (QuotientAddGroup.mk (x *ᵥ ((0 : intVec L n) : Fin n → L))) := by
    rw [key, key]
    simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero]
    exact (QuotientAddGroup.eq_zero_iff _).2 hyu
  have h1 := hinj ⟨u0, rfl⟩ ⟨0, rfl⟩ h0
  simp only [AddSubgroup.coe_zero, Matrix.mulVec_zero, QuotientAddGroup.mk_zero] at h1
  exact (QuotientAddGroup.eq_zero_iff _).1 h1

end GlobalTheory.Hk3.HoweDuality

end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  atlas_forward_decl GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq
end

section
section
open Matrix

namespace GlobalTheory

theorem columns_indepMod :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  intro L _ _ ϖ hϖ n n' x V a H d hd hdiv j
  classical
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hϖi : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  set c : Fin n → L := fun k => if h : 0 < a k then d ⟨k, h⟩ * ϖ ^ (a k - 1) else 0 with hc
  have hcint : ∀ k, c k ∈ Formalism.UG.intL L := by
    intro k; simp only [hc]; split_ifs
    · exact mul_mem (hd _) (pow_mem hϖi _)
    · exact zero_mem _
  have hsum : ϖ • c = ∑ i : {j : Fin n // 0 < a j}, d i • Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)) := by
    funext k
    rw [Finset.sum_apply]
    by_cases hk : 0 < a k
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · obtain ⟨m, hm⟩ : ∃ m, a k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
        simp [hc, hk, hm]; ring
      · intro b _ hb
        have : k ≠ (b : Fin n) := fun h => hb (Subtype.ext h.symm)
        simp [Pi.single_apply, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hc, hk]
      · intro i _
        have : k ≠ (i : Fin n) := fun h => hk (h ▸ i.2)
        simp [Pi.single_apply, this]
  have hlin : ϖ • (x *ᵥ (V *ᵥ c)) = ∑ i : {j : Fin n // 0 < a j}, d i • (x *ᵥ (V *ᵥ Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)))) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hsum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul]
  have hw : ∀ r, (x *ᵥ (V *ᵥ c)) r ∈ Formalism.UG.intL L := by
    intro r
    obtain ⟨b, hb, hbe⟩ := hdiv r
    have h1 := congrFun hlin r
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h1
    rw [← h1, pow_one] at hbe
    rw [mul_left_cancel₀ hϖ0 hbe]; exact hb
  obtain ⟨b, hb, hbe⟩ := (H c hcint).1 hw j
  refine ⟨b, hb, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := Nat.exists_eq_succ_of_ne_zero j.2.ne'
  simp only [hc, dif_pos j.2, hm, Nat.add_sub_cancel] at hbe
  apply mul_right_cancel₀ (pow_ne_zero m hϖ0)
  rw [hbe]; ring

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  atlas_forward_decl GlobalTheory.columns_indepMod
end

section
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_smul_smul (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (s t : L) (u v : Fin n → L) :
    Formalism.UG.hform σ J (s • u) (t • v) = σ s * t * Formalism.UG.hform σ J u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_single_int {n : ℕ} (V : Matrix (Fin n) (Fin n) L) (hV : ∀ i j, V i j ∈ Formalism.UG.intL L) (i : Fin n) :
    ∀ r, (V *ᵥ Pi.single i (1 : L)) r ∈ Formalism.UG.intL L := by
  intro r
  have : (V *ᵥ Pi.single i (1 : L)) r = V r i := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]; exact hV r i

theorem single_eq_smul {n : ℕ} (i : Fin n) (c : L) : (Pi.single i c : Fin n → L) = c • Pi.single i (1 : L) := by
  ext r; by_cases h : r = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_class_columns : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  intro L _ _ ϖ σ q hU n n' JT x y V a hV hiff hG i j
  have hϖv : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact le_of_lt (by decide)
  have hϖ : ϖ ∈ Formalism.UG.intL L := hϖv
  set k := max (a i) (a j) with hk
  set c : L := ϖ ^ k with hc
  have hcI : c ∈ Formalism.UG.intL L := (Formalism.UG.intL L).pow_mem hϖ _

  have hcond : ∀ l, a l ≤ k → ∀ r, (x *ᵥ (c • (V *ᵥ Pi.single l (1 : L)))) r ∈ Formalism.UG.intL L := by
    intro l hl
    have hI : ∀ t, (Pi.single l c : Fin n → L) t ∈ Formalism.UG.intL L := by
      intro t; by_cases h : t = l
      · subst h; simpa using hcI
      · simp [Pi.single_apply, h, (Formalism.UG.intL L).zero_mem]
    have := (hiff (Pi.single l c) hI).mpr (by
      intro t; by_cases h : t = l
      · subst h
        refine ⟨ϖ ^ (k - a t), (Formalism.UG.intL L).pow_mem hϖ _, ?_⟩
        simp [hc, ← pow_add, Nat.add_sub_cancel' hl]
      · simpa [Pi.single_apply, h] using dvdPow_zero ϖ (a t))
    rwa [single_eq_smul, mulVec_smul] at this
  have hD := hG _ _ (mulVec_single_int V hV i) (mulVec_single_int V hV j) c hcI
    (hcond i (le_max_left _ _)) (hcond j (le_max_right _ _))
  refine ⟨_, hD, ?_⟩
  rw [single_eq_smul i, single_eq_smul j, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
    hform_smul_smul, hform_smul_smul, map_pow, hU.2.2.1, hc, ← mul_sub, ← mul_assoc, ← pow_add, ← pow_add,
    min_add_max]

end GlobalTheory.Hk3.IntWitt

end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClass_elementaryDivisor_columns_congr : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  atlas_forward_decl GlobalTheory.Hk3.IntWitt.gram_class_columns
end

section
section
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_intUnitary_of_gramClass : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q n n' JS JT hU hq hJS hJT hS hT x y _hG hA hGr hidx
  classical
  have hvϖ := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖint : ϖ ∈ Formalism.UG.intL L := by
    unfold Formalism.UG.intL
    rw [Valuation.mem_integer_iff, hvϖ]
    exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by decide)
  have mulVec_int : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) (v : Fin b → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, v j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro a b M v hM hv i
    simp only [Matrix.mulVec, dotProduct]
    exact (Formalism.UG.intL L).sum_mem fun j _ => (Formalism.UG.intL L).mul_mem (hM i j) (hv j)
  obtain ⟨V, hV, a, hxV⟩ := GlobalTheory.T.exists_elementaryDivisors_integral_preimage_lattice L ϖ hvϖ n n' x
  obtain ⟨g0, hg0⟩ := hV
  have hVint : ∀ i j, (V : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  have hVinv : ∀ i j, ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (Formalism.UG.intL L)) : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  set Vm : Matrix (Fin n) (Fin n) L := (V : Matrix (Fin n) (Fin n) L) with hVm
  have hyV : ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (y *ᵥ (Vm *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
    intro c hc
    have hu : ∀ i, (Vm *ᵥ c) i ∈ Formalism.UG.intL L := mulVec_int Vm c hVint hc
    rw [← hxV c hc]
    exact ⟨fun h => GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq L ϖ σ q hU n n' x y hA.1 hidx _ hu h, fun h => hA.1 _ hu h⟩
  let ej : Fin n → Fin n → L := fun j => Pi.single j (ϖ ^ a j)
  have hej_int : ∀ j k, ej j k ∈ Formalism.UG.intL L := by
    intro j k
    by_cases h : k = j
    · subst h; simpa [ej] using (Formalism.UG.intL L).pow_mem hϖint (a k)
    · simp [ej, Pi.single_apply, h]
  have hej_dvd : ∀ j k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a k) (ej j k) := by
    intro j k
    by_cases h : k = j
    · subst h; exact ⟨1, (Formalism.UG.intL L).one_mem, by simp [ej]⟩
    · simpa [ej, Pi.single_apply, h] using GlobalTheory.Hk3.IntWitt.dvdPow_zero ϖ (a k)
  let zx : {j : Fin n // 0 < a j} → Fin n' → L := fun j => x *ᵥ (Vm *ᵥ ej j)
  let zy : {j : Fin n // 0 < a j} → Fin n' → L := fun j => y *ᵥ (Vm *ᵥ ej j)
  have hzx : ∀ j r, zx j r ∈ Formalism.UG.intL L := fun j => (hxV _ (hej_int j)).mpr (hej_dvd j)
  have hzy : ∀ j r, zy j r ∈ Formalism.UG.intL L := fun j => (hyV _ (hej_int j)).mpr (hej_dvd j)
  have hix : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zx := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' x Vm a hxV
  have hiy : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zy := GlobalTheory.T.elementaryDivisor_columns_independentModUniformizer L ϖ hvϖ n n' y Vm a hyV
  have hgr := GlobalTheory.T.gramClass_elementaryDivisor_columns_congr L ϖ σ q hU n n' JT x y Vm a hVint hxV hGr
  obtain ⟨h, hh, hcong⟩ := GlobalTheory.T.integralWittTheorem_mod_uniformizerPow L ϖ σ q hU hq n' JT hJT hT {j : Fin n // 0 < a j} (fun j => a j) zx zy
    (fun j => j.2) hzx hzy hix hiy (fun i j => hgr i j)
  refine ⟨h, hh, ?_⟩
  set H : Matrix (Fin n') (Fin n') L := ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hH
  have hHint : ∀ i j, H i j ∈ Formalism.UG.intL L := by
    obtain ⟨h0, hh0⟩ := hh
    intro i j; rw [hH, ← hh0]; exact ((h0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set M := y - H * x with hM
  have hMv : ∀ w : Fin n → L, M *ᵥ w = y *ᵥ w - H *ᵥ (x *ᵥ w) := by
    intro w; rw [hM, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have hcol : ∀ j i, (M *ᵥ (Vm *ᵥ Pi.single j 1)) i ∈ Formalism.UG.intL L := by
    intro j i
    by_cases ha : a j = 0
    · have he : Pi.single j (1 : L) = ej j := by simp [ej, ha]
      rw [he, hMv]
      exact (Formalism.UG.intL L).sub_mem ((hyV _ (hej_int j)).mpr (hej_dvd j) i)
        (mulVec_int H _ hHint ((hxV _ (hej_int j)).mpr (hej_dvd j)) i)
    · have hpos : 0 < a j := Nat.pos_of_ne_zero ha
      obtain ⟨b, hb, hbe⟩ := hcong ⟨j, hpos⟩ i
      have he : ej j = ϖ ^ a j • Pi.single j (1 : L) := by
        funext k; simp [ej, Pi.single_apply]
      have key : ϖ ^ a j * (M *ᵥ (Vm *ᵥ Pi.single j 1)) i = ϖ ^ a j * (-b) := by
        have : (M *ᵥ (Vm *ᵥ ej j)) i = -((H *ᵥ zx ⟨j, hpos⟩) i - zy ⟨j, hpos⟩ i) := by
          rw [hMv]; simp only [zx, zy, Pi.sub_apply]; ring
        rw [he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
        rw [this, hbe]; ring
      have := mul_left_cancel₀ (pow_ne_zero _ hϖ0) key
      rw [this]; exact (Formalism.UG.intL L).neg_mem hb
  intro i r
  have hMe : M = (M * Vm) * ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.mul_assoc, hVm, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hMe, Matrix.mul_apply]
  refine (Formalism.UG.intL L).sum_mem fun k _ => (Formalism.UG.intL L).mul_mem ?_ (hVinv k r)
  have hc := hcol k i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at hc

end GlobalTheory.Hk3.HoweG

end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intUnitary_of_gramClass_alt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  atlas_forward_decl GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass
end

section
section
noncomputable section

namespace GlobalTheory.Hk3.HoweG

theorem gramClass_orbit_mod_lower : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs hvac hspan x hx
  classical
  obtain ⟨C, c, hxC, hC, hpw, hsum⟩ := GlobalTheory.T.gram_class_translate_sum_mem_span_selfDual_lattice_vacua L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac x hx
  have hψ0 : ∀ e : L, ψ e ≠ 0 := fun e h => by
    have h2 : ψ e * ψ (-e) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [h, zero_mul] at h2; exact zero_ne_one h2
  have hint_mul : ∀ (u : Matrix (Fin n') (Fin n) L) (k : GL (Fin n) L), (∀ i j, u i j ∈ Formalism.UG.intL L) →
      k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j, (u * (k : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro u k hu hk i j
    obtain ⟨k0, rfl⟩ := hk
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hu i l) ((k0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) l j).2

  have hvacSS : Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} ≤
      Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
    rw [Submodule.span_le]
    rintro w ⟨a, ha, hw⟩
    obtain ⟨g, k, hk, hak⟩ := GlobalTheory.T.selfDual_lattice_eq_unitary_mul_integralGL L ϖ σ q n JS hP.unr hP.odd hP.intS hP.hermS a ha
    have hw' : GlobalTheory.Hk3.LocVac ρ (ω (g⁻¹, 1) w) := by
      intro u hu
      have h1 := hP.norm g⁻¹ 1 (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
      have h2 : ρ (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w := by
        have := hw (u * (k : Matrix (Fin n) (Fin n) L)) (hint_mul u k hu hk)
        rw [hak] at this
        simpa [Matrix.mul_assoc, mul_inv_rev] using this
      have h3 := congrArg (fun F : Module.End ℂ M => F w) h1
      simp only [Module.End.mul_apply, h2] at h3
      have e : (((1 : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((((g⁻¹ : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = u := by
        rw [Subgroup.coe_inv, inv_inv, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [e] at h3
      exact h3.symm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (GlobalTheory.T.localLatticeVacuum_mem_span_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac hspan _ hw')
    have hww : w = t • ω (g, 1) s := by
      have e1 : ω (g, 1) (ω (g⁻¹, 1) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [← e1, ← ht, map_smul]
    rw [SetLike.mem_coe, hww]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  refine ⟨∑ y ∈ C, c y • ρ y s, hvacSS hsum,
    ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ?_, rfl⟩)
    obtain ⟨hyC, hne⟩ := Finset.mem_filter.1 hy
    exact lt_of_le_of_ne (GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel L ϖ σ q n' n x y hP.unr (hC y hyC).2.1.1) hne
  have hsplit : ∑ y ∈ C, c y • ρ y s - ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s =
      ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s := by
    rw [← Finset.sum_filter_add_sum_filter_not C (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x)]
    exact add_sub_cancel_right _ _
  rw [hsplit]

  have hshift : ∀ y y' : Matrix (Fin n') (Fin n) L, (∀ i j, (y - y') i j ∈ Formalism.UG.intL L) → ∃ ζ : ℂ, ζ ≠ 0 ∧ ρ y' s = ζ • ρ y s := by
    intro y y' hl
    refine ⟨ψ ((GlobalTheory.Hk3.locH σ δ JS JT y' (y - y') + σ (GlobalTheory.Hk3.locH σ δ JS JT y' (y - y'))) / 2), hψ0 _, ?_⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul y' (y - y'))
    simp only [Module.End.mul_apply, hvac _ hl, LinearMap.smul_apply, add_sub_cancel] at h1
    exact h1
  refine ⟨Submodule.sum_mem _ fun y hy => ?_, ?_⟩
  · obtain ⟨hyC, heq⟩ := Finset.mem_filter.1 hy
    obtain ⟨h, hh, hyl⟩ := GlobalTheory.T.exists_intUnitary_of_gramClass_alt L ϖ σ q n n' JS JT hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT x y hx (hC y hyC).2.1 (hC y hyC).2.2 heq
    obtain ⟨ζ, hζ, hζe⟩ := hshift y (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) hyl
    have : ρ y s = ζ⁻¹ • ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
      rw [hζe, smul_smul, inv_mul_cancel₀ hζ, one_smul]
    rw [this, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh, rfl⟩)
  ·
    have hI := GlobalTheory.Hk3.locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
    set P := C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x) with hPdef
    have hxP : x ∈ P := Finset.mem_filter.2 ⟨hxC, rfl⟩
    set F := fun cl : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = cl ∧ w = ρ x s} with hF
    have hmem : ∀ y : Matrix (Fin n') (Fin n) L, ∀ t : ℂ, t • ρ y s ∈ F (QuotientAddGroup.mk y) :=
      fun y t => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl, rfl⟩)
    have hrest : ∑ y ∈ P.erase x, c y • ρ y s ∈ ⨆ (j) (_ : j ≠ (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n)), F j := by
      refine Submodule.sum_mem _ fun y hy => ?_
      have hyx : y ≠ x := Finset.ne_of_mem_erase hy
      have hyC : y ∈ C := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hy)).1
      have hne : (QuotientAddGroup.mk y : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ≠ QuotientAddGroup.mk x := by
        intro he
        apply hpw y hyC x hxC hyx
        have := (QuotientAddGroup.eq).1 he.symm
        have h2 : y - x = -x + y := by abel
        rw [h2]; exact this
      exact (le_iSup₂_of_le (QuotientAddGroup.mk y) hne le_rfl : F (QuotientAddGroup.mk y) ≤ _) (hmem y (c y))
    intro h0
    rw [← Finset.add_sum_erase P _ hxP] at h0
    have hxx : c x • ρ x s = 0 := by
      have hd := (hI (QuotientAddGroup.mk x))
      rw [Submodule.disjoint_def] at hd
      apply hd _ (hmem x (c x))
      have : c x • ρ x s = -(∑ y ∈ P.erase x, c y • ρ y s) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact neg_mem hrest
    have hcx := (hC x hxC).1
    rw [smul_eq_zero] at hxx
    rcases hxx with h | h
    · exact hcx h
    · apply hs
      have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul (-x) x)
      simp only [Module.End.mul_apply, h, map_zero, neg_add_cancel, hP.rho_zero, LinearMap.smul_apply, Module.End.one_apply] at h1
      exact (smul_eq_zero.1 h1.symm).resolve_left (hψ0 _)

end GlobalTheory.Hk3.HoweG

end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  atlas_forward_decl GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  first | exact @GlobalTheory.Hk3.HoweSwap.locPair_swap | exact GlobalTheory.Hk3.HoweSwap.locPair_swap | (intros; apply GlobalTheory.Hk3.HoweSwap.locPair_swap <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

section Glue

open Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem int_entry {m : ℕ} {h : GL (Fin m) L} (hh : h ∈ GLint (Fin m) (intL L)) (i j : Fin m) :
    (h : Matrix (Fin m) (Fin m) L) i j ∈ intL L := by
  obtain ⟨k, rfl⟩ := hh; simp [Formalism.UG.bc]

theorem mul_mem_intMat {a b : ℕ} {h : GL (Fin a) L} (hh : h ∈ GLint (Fin a) (intL L)) {u : Matrix (Fin a) (Fin b) L}
    (hu : u ∈ intMat L a b) : (h : Matrix (Fin a) (Fin a) L) * u ∈ intMat L a b := by
  rw [mem_intMat] at hu ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (int_entry hh i k) (hu k j)

def lmulQ {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) :
    Matrix (Fin a) (Fin b) L ⧸ intMat L a b →+ Matrix (Fin a) (Fin b) L ⧸ intMat L a b :=
  QuotientAddGroup.map _ _
    { toFun := fun x => (h : Matrix (Fin a) (Fin a) L) * x, map_zero' := Matrix.mul_zero _,
      map_add' := Matrix.mul_add _ }
    (fun _ hu => mul_mem_intMat hh hu)

theorem lmulQ_mk {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (x : Matrix (Fin a) (Fin b) L) :
    lmulQ h hh (QuotientAddGroup.mk x) = QuotientAddGroup.mk ((h : Matrix (Fin a) (Fin a) L) * x) := rfl

theorem lmulQ_mul {a b : ℕ} (h h' : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (hh' : h' ∈ GLint (Fin a) (intL L))
    (hhh : h * h' ∈ GLint (Fin a) (intL L)) (c : Matrix (Fin a) (Fin b) L ⧸ intMat L a b) :
    lmulQ (h * h') hhh c = lmulQ h hh (lmulQ h' hh' c) := by
  induction c using QuotientAddGroup.induction_on with
  | H x => simp only [lmulQ_mk, Units.val_mul, Matrix.mul_assoc]

abbrev KT (σ : L →+* L) {a : ℕ} (J : Matrix (Fin a) (Fin a) L) : Subgroup (UJ σ J) :=
  (GLint (Fin a) (intL L)).comap (UJ σ J).subtype

def actQ (σ : L →+* L) {a b : ℕ} (J : Matrix (Fin a) (Fin a) L) :
    MulAction (KT σ J) (Matrix (Fin a) (Fin b) L ⧸ intMat L a b) where
  smul k c := lmulQ ((k : UJ σ J) : GL (Fin a) L) (Subgroup.mem_comap.1 k.2) c
  one_smul c := by
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      show lmulQ _ _ _ = _
      simp [lmulQ]
  mul_smul k k' c :=
    lmulQ_mul (((k : UJ σ J) : GL (Fin a) L)) (((k' : UJ σ J) : GL (Fin a) L)) _ _ _ c

theorem psi_ne_zero (ψ : AddChar L ℂ) (a : L) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end Glue

section Data

open Formalism.UG

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

theorem rho_add_int (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (x u : Matrix (Fin n') (Fin n) L) (hu : u ∈ intMat L n' n) : ∃ c : ℂ, c ≠ 0 ∧ ρ (x + u) s = c • ρ x s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x u)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hs u ((mem_intMat u).1 hu)] at h1
  obtain ⟨c, hc, h2⟩ : ∃ c : ℂ, c ≠ 0 ∧ ρ x s = c • ρ (x + u) s := ⟨_, psi_ne_zero ψ _, h1⟩
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem rho_mem_of_mk_eq (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    {x y : Matrix (Fin n') (Fin n) L}
    (hxy : (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk y) :
    ρ x s ∈ Submodule.span ℂ {ρ y s} := by
  have hu : -y + x ∈ intMat L n' n := QuotientAddGroup.eq.1 hxy.symm
  obtain ⟨c, -, hc⟩ := rho_add_int hP hs y (-y + x) hu
  rw [add_neg_cancel_left] at hc
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem om_rho (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (h : UJ σ (JT : Matrix (Fin n') (Fin n') L)) (hh : (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L))
    (x : Matrix (Fin n') (Fin n) L) : ω (1, h) (ρ x s) = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.norm 1 h x)
  have hfix := hP.fix 1 h (by simpa using (GLint (Fin n) (intL L)).one_mem) hh s hs
  simp only [Module.End.mul_apply] at h1
  rw [h1, hfix]
  have h1' : (((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) = 1 := by
    rw [OneMemClass.coe_one, inv_one]
  rw [h1', Units.val_one, Matrix.mul_one]

theorem step (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) (s : M) (hs0 : s ≠ 0) (hs : GlobalTheory.Hk3.LocVac ρ s)
    (hspan : Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤) (x : Matrix (Fin n') (Fin n) L)
    (hfix : ∃ w : M, w ≠ 0 ∧ (∀ h : UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L) → ω (1, h) w = w) ∧ w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) :
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, latIdx y < latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  obtain ⟨l, hl, hg⟩ := GlobalTheory.T.exists_int_gram_of_fixed_alt L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan x hfix
  obtain ⟨v, hv, u, hu, h1, h2⟩ := GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan (x - l) hg
  have hidx : latIdx (x - l) = latIdx x := by
    rw [sub_eq_add_neg]; exact (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).1 _ (neg_mem hl)
  refine ⟨v, hv, u, by rwa [hidx] at hu, ?_, h2⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨h, hh, rfl⟩
  have hm : (QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (x - l)) :
      Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) := by
    rw [QuotientAddGroup.eq, Matrix.mul_sub]
    have : -(((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l) +
        ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x = ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l := by abel
    rw [this]; exact mul_mem_intMat hh hl
  have hmem : ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} :=
    Submodule.subset_span ⟨h, hh, rfl⟩
  exact (Submodule.span_singleton_le_iff_mem _ _).2 hmem (rho_mem_of_mk_eq hP hs hm)

end Data

section Half

open Formalism.UG

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

theorem fixed_mem_span (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) (s : M) (hs0 : s ≠ 0) (hs : GlobalTheory.Hk3.LocVac ρ s)
    (hspan : Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤) (w : M)
    (hw : ∀ h : UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L) → ω (1, h) w = w) :
    w ∈ Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
  letI := actQ (b := n) σ (JT : Matrix (Fin n') (Fin n') L)
  let V : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → Submodule ℂ M := fun c =>
    Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
      (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = c ∧ w = ρ x s}
  let π : KT σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M :=
    (ω.comp (MonoidHom.inr _ _)).comp (KT σ (JT : Matrix (Fin n') (Fin n') L)).subtype
  let μ : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → ℕ := fun c => latIdx (Quotient.out c)
  let S := Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s)
  have hπ_apply : ∀ k v, π k v = ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) v := fun _ _ => rfl
  have hsmul : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) (x : Matrix (Fin n') (Fin n) L),
      k • (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) =
        QuotientAddGroup.mk ((((k : UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) := fun _ _ => rfl
  have hμmk : ∀ x, μ (QuotientAddGroup.mk x) = latIdx x := by
    intro x
    have hu : -Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) + x ∈ intMat L n' n :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n (Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n))).1 _ hu
    rw [add_neg_cancel_left] at this
    exact this.symm
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := fun x => Submodule.subset_span ⟨x, rfl, rfl⟩
  have hVle : ∀ x, V (QuotientAddGroup.mk x) ≤ Submodule.span ℂ {ρ x s} := by
    intro x
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact rho_mem_of_mk_eq hP hs hy
  have hind := GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs
  have htop : (⨆ c, V c) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_iSup_of_mem (QuotientAddGroup.mk x) (hmemV x)
  have hline : ∀ c, ∃ v : M, V c ≤ Submodule.span ℂ {v} := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x => exact ⟨ρ x s, hVle x⟩
  have hπ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, (V c).map (π k) ≤ V (k • c) := by
    intro k c
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨x, rfl, rfl⟩, rfl⟩
    rw [hπ_apply, om_rho hP hs _ (Subgroup.mem_comap.1 k.2), hsmul]
    exact hmemV _
  have hμ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, μ (k • c) = μ c := by
    intro k c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [hsmul, hμmk, hμmk]
      exact (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).2 _ (Subgroup.mem_comap.1 k.2)
  have hS : ∀ v ∈ S, ∀ k, π k v = v := by
    intro v hv k
    have hle : S ≤ LinearMap.eqLocus (π k) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      show π k (ω (g, 1) s) = ω (g, 1) s
      rw [hπ_apply, ← Module.End.mul_apply, ← map_mul]
      have e : ((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)), (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) * (g, 1) =
          (g, 1) * (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) := by
        simp
      rw [e, map_mul, Module.End.mul_apply,
        hP.fix 1 _ (by simpa using (GLint (Fin n) (intL L)).one_mem) (Subgroup.mem_comap.1 k.2) s hs]
    exact hle hv
  have hstep : ∀ c, (∃ w : M, w ≠ 0 ∧ (∀ k, π k w = w) ∧ w ∈ ⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ c), V j,
        v - u ∈ (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) ∧ v - u ≠ 0 := by
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      have horb1 : (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) ≤
          Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} := by
        refine iSup_le fun k => ?_
        rw [hsmul]
        refine (hVle _).trans ?_
        exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ⟨k, Subgroup.mem_comap.1 k.2, rfl⟩)
      have horb2 : Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ≤
          (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, hh, rfl⟩
        refine Submodule.mem_iSup_of_mem (⟨h, hh⟩ : KT σ (JT : Matrix (Fin n') (Fin n') L)) ?_
        rw [hsmul]
        exact hmemV _
      obtain ⟨w, hw0, hwf, hwm⟩ := hc
      obtain ⟨v, hv, u, hu, h1, h2⟩ := step hP s hs0 hs hspan x ⟨w, hw0, fun h hh => hwf ⟨h, hh⟩, horb1 hwm⟩
      refine ⟨v, hv, u, ?_, horb2 h1, h2⟩
      refine Submodule.span_le.2 ?_ hu
      rintro _ ⟨y, hy, rfl⟩
      refine Submodule.mem_iSup_of_mem (QuotientAddGroup.mk y) (Submodule.mem_iSup_of_mem ?_ (hmemV y))
      rw [hμmk, hμmk]
      exact hy
  exact GlobalTheory.T.invariant_mem_of_orbit_height_separation π V hind htop hline hπ μ hμ S hS hstep w (fun k => hw k (Subgroup.mem_comap.1 k.2))

end Half

end GlobalTheory.Hk3.HoweDuality

namespace GlobalTheory.Hk3

open GlobalTheory.Hk3.HoweDuality

theorem howeUnram_holds : HoweUnram := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan
  refine ⟨?_, fixed_mem_span hP s hs0 hs hspan⟩
  intro w hw
  obtain ⟨hP', hv', hsp'⟩ := GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint L ϖ σ q δ n n' JS JT ψ M ρ ω hP
  have := fixed_mem_span hP' s hs0 (hv' s hs) (hsp' s hspan) w (fun h hh => by simpa using hw h hh)
  simpa using this

end GlobalTheory.Hk3

end
end
