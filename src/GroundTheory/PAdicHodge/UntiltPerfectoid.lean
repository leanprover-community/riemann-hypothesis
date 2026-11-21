import Mathlib
import GroundTheory.PAdicHodge.UntiltField
import GroundTheory.PAdicHodge.TiltAlgebra
import GroundTheory.PAdicHodge.PerfectoidField

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]

omit [IsUltrametricDist k] [IsUltrametricDist E] in

theorem exists_sub_far_of_isClosed {U : Submodule k E} (hU : IsClosed (U : Set E)) {x : E}
    (hx : x ∉ U) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ u ∈ U, ∀ u' ∈ U, s * ‖x - u‖ ≤ ‖x - u - u'‖ := by
  have hne : (U : Set E).Nonempty := ⟨0, U.zero_mem⟩
  have hd : 0 < Metric.infDist x U := (hU.notMem_iff_infDist_pos hne).1 hx
  have hlt : Metric.infDist x U < Metric.infDist x U / s := by
    rw [lt_div_iff₀ hs0]; nlinarith
  obtain ⟨u, huU, hu⟩ := (Metric.infDist_lt_iff hne).1 hlt
  refine ⟨u, huU, fun u' hu' => ?_⟩
  have h1 : Metric.infDist x U ≤ dist x (u + u') :=
    Metric.infDist_le_dist_of_mem (U.add_mem huU hu')
  rw [dist_eq_norm, ← sub_sub] at h1
  rw [dist_eq_norm] at hu
  have h2 := (lt_div_iff₀ hs0).1 hu
  nlinarith

omit [IsUltrametricDist k] in

theorem le_norm_smul_add_of_far {U : Submodule k E} {w : E} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hw : ∀ u' ∈ U, s * ‖w‖ ≤ ‖w - u'‖) (a : k) {u : E} (hu : u ∈ U) :
    s * ‖a • w‖ ≤ ‖a • w + u‖ ∧ s * ‖u‖ ≤ ‖a • w + u‖ := by
  have h1 : s * ‖a • w‖ ≤ ‖a • w + u‖ := by
    by_cases ha : a = 0
    · simp [ha]
    · have he : a • w + u = a • (w - (-a⁻¹ • u)) := by
        rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ ha, neg_one_smul, sub_neg_eq_add]
      rw [he, norm_smul, norm_smul]
      have := hw (-a⁻¹ • u) (U.smul_mem _ hu)
      nlinarith [norm_nonneg a]
  refine ⟨h1, ?_⟩
  have h2 : ‖u‖ ≤ max ‖a • w + u‖ ‖a • w‖ := by
    have := IsUltrametricDist.norm_add_le_max (a • w + u) (-(a • w))
    have e : a • w + u + -(a • w) = u := by abel
    rwa [e, norm_neg] at this
  rcases le_max_iff.1 h2 with h | h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]

variable [CompleteSpace k]

theorem exists_orthogonal_fin (n : ℕ) : ∀ (v : Fin n → E), LinearIndependent k v →
    ∀ {τ : ℝ}, 0 < τ → τ < 1 →
    ∃ w : Fin n → E, (∀ i, w i ≠ 0) ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : Fin n → k) (i : Fin n), τ * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  induction n with
  | zero =>
    intro v _ τ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ i => i.elim0⟩
  | succ n ih =>
    intro v hv τ hτ0 hτ1
    set s := Real.sqrt τ with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hτ0
    have hs1 : s < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt hτ0.le hτ1
    have hss : s * s = τ := Real.mul_self_sqrt hτ0.le
    obtain ⟨w', hw'0, hw'mem, hw'⟩ :=
      ih (fun i => v i.castSucc) (hv.comp _ (Fin.castSucc_injective n)) hs0 hs1
    set U := Submodule.span k (Set.range w') with hUdef
    have : FiniteDimensional k U := FiniteDimensional.span_of_finite k (Set.finite_range w')
    have hUc : IsClosed (U : Set E) := U.closed_of_finiteDimensional
    have hrange : (Set.range fun i : Fin n => v i.castSucc) = v '' Set.range Fin.castSucc :=
      Set.range_comp v Fin.castSucc
    have hUv : U ≤ Submodule.span k (Set.range fun i : Fin n => v i.castSucc) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hw'mem)
    have hvv : Submodule.span k (Set.range fun i : Fin n => v i.castSucc) ≤
        Submodule.span k (Set.range v) :=
      Submodule.span_mono (Set.range_comp_subset_range _ _)
    have hx : v (Fin.last n) ∉ U := by
      intro h
      have h' := hUv h
      rw [hrange] at h'
      exact hv.notMem_span_image (s := Set.range Fin.castSucc) (x := Fin.last n)
        (by rintro ⟨j, hj⟩; exact (Fin.castSucc_lt_last j).ne hj) h'
    obtain ⟨u, huU, hu⟩ := exists_sub_far_of_isClosed hUc hx hs0 hs1
    set x := v (Fin.last n) - u with hxdef
    have hx0 : x ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero] at h
      rw [h]; exact huU
    have hfar : ∀ u' ∈ U, s * ‖x‖ ≤ ‖x - u'‖ := hu
    refine ⟨(Fin.snoc w' x : Fin (n + 1) → E), ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hx0
      | cast i => simpa using hw'0 i
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨Fin.last n, rfl⟩) (hvv (hUv huU))
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact hvv (hw'mem i)
    · intro c i
      have hsum : ∑ j, c j • (Fin.snoc w' x : Fin (n + 1) → E) j =
          c (Fin.last n) • x + ∑ j : Fin n, c j.castSucc • w' j := by
        rw [Fin.sum_univ_castSucc, add_comm]
        simp
      have hu'U : ∑ j : Fin n, c j.castSucc • w' j ∈ U :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨h1, h2⟩ := le_norm_smul_add_of_far hs0 hs1.le hfar (c (Fin.last n)) hu'U
      rw [hsum]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        have : τ * ‖c (Fin.last n) • x‖ ≤ s * ‖c (Fin.last n) • x‖ := by
          rw [← hss]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
        linarith
      | cast i =>
        simp only [Fin.snoc_castSucc]
        have h3 := hw' (fun j => c j.castSucc) i
        rw [← hss, mul_assoc]
        nlinarith

theorem exists_orthogonal_of_linearIndependent {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : LinearIndependent k v) {t : ℝ} (ht : t < 1) :
    ∃ w : ι → E, LinearIndependent k w ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : ι → k) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  set τ := max t (1 / 2) with hτ
  have hτ0 : 0 < τ := lt_max_of_lt_right (by norm_num)
  have hτ1 : τ < 1 := max_lt ht (by norm_num)
  let e := Fintype.equivFin ι
  obtain ⟨w, hw0, hwmem, hw⟩ := exists_orthogonal_fin (Fintype.card ι) (v ∘ e.symm)
    (hv.comp _ e.symm.injective) hτ0 hτ1
  have hsum : ∀ c : ι → k, ∑ j, c j • w (e j) = ∑ j, (c ∘ e.symm) j • w j := by
    intro c
    have := e.sum_comp (fun j => (c ∘ e.symm) j • w j)
    simpa using this
  have horth : ∀ (c : ι → k) (i : ι), τ * ‖c i • w (e i)‖ ≤ ‖∑ j, c j • w (e j)‖ := by
    intro c i
    rw [hsum]
    simpa using hw (c ∘ e.symm) (e i)
  refine ⟨fun i => w (e i), ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := horth g i
    rw [hg, norm_zero] at h
    have h0 : ‖g i • w (e i)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (g i • w (e i))]) (norm_nonneg _)
    rw [norm_eq_zero, smul_eq_zero] at h0
    exact h0.resolve_right (hw0 (e i))
  · intro i
    have := hwmem (e i)
    rwa [e.symm.surjective.range_comp v] at this
  · intro c i
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans (horth c i)

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem exists_lt_mul_mul_lt_one {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ q < s * s * s := by
  refine ⟨(3 + q) / 4, by linarith, by linarith, ?_⟩
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 27 - 10 * q - q * q := by nlinarith
  nlinarith [mul_pos h1 h2]

section

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

omit [IsUltrametricDist K] [IsUltrametricDist C] [Fact p.Prime] [IsPerfectoidField K p]
  [IsPerfectoidField C p] in

theorem norm_natCast_algebra : ‖(p : C)‖ = ‖(p : K)‖ := by
  rw [← map_natCast (algebraMap K C), norm_algebraMap']

omit [NontriviallyNormedField K] [IsUltrametricDist K] [NontriviallyNormedField C] [NormedAlgebra K C]
  [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p] in

theorem norm_eq_of_norm_sub_lt {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rw [sub_add_cancel, max_eq_right h.le] at this
  exact this

theorem lt_norm_sum_smul_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hp : ‖(p : K)‖ ≤ t * r * ρ) {l : ι → K} (hl1 : ∀ i, ‖l i‖ ≤ 1) {j : ι} (hj : ρ < ‖l j‖) :
    t * r * ρ < ‖∑ i, l i • tiltSharp C p (w i)‖ := by
  classical
  have hwj0 : 0 < ‖w j‖ := hr.trans_lt (hwr j)

  have ht1 : t ≤ 1 := by
    have e : ∑ j', (Pi.single j (1 : K♭) : ι → K♭) j' • w j' = w j := by
      rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    have := hw (Pi.single j 1) j
    rw [e, Pi.single_eq_same, one_smul] at this
    exact le_of_mul_le_mul_right (by linarith) hwj0
  have hr1 : r < 1 := (hwr j).trans_le (hw1 j)
  have htr : t * r ≤ 1 := by nlinarith
  have hpρ : ‖(p : K)‖ ≤ ρ := hp.trans (by nlinarith)
  have hpl : ‖(p : K)‖ < ‖l j‖ := hpρ.trans_lt hj

  have hA : ∀ i, ∃ a : 𝒪K♭, ‖((a.untilt : normInteger K) : K) - l i‖ ≤ ‖(p : K)‖ := fun i => by
    obtain ⟨a, ha⟩ := exists_mk_untilt_eq (p := p)
      (⟨l i, mem_normInteger.2 (hl1 i)⟩ : normInteger K)
    exact ⟨a, mk_eq_mk_iff_norm_sub_le.1 ha⟩
  choose a ha using hA
  choose b hb using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hw1 i)
  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C) with hφ
  set d : ι → 𝒪C♭ := fun i => φ (a i) * b i with hd
  have hdw : ∀ i, algebraMap 𝒪C♭ C♭ (d i) = algebraMap 𝒪K♭ K♭ (a i) • w i := by
    intro i
    rw [Algebra.smul_def, algebraMap_tilt_eq, tiltMap_algebraMap, ← hb i, ← map_mul]
  have hsharp : ∀ i, tiltSharp C p (w i) = ((b i).untilt : C) := by
    intro i; rw [← hb i, tiltSharp_algebraMap]
  have hdu : ∀ i, ((d i).untilt : C) = algebraMap K C ((a i).untilt : K) * tiltSharp C p (w i) := by
    intro i
    rw [hd, untilt_mul, Subring.coe_mul, coe_untilt_preTiltMap, hsharp]
  set A : C := ((∑ i, d i).untilt : C) with hA

  have hAn : ‖A‖ = ‖∑ i, algebraMap 𝒪K♭ K♭ (a i) • w i‖ := by
    rw [hA, ← tiltSharp_algebraMap, norm_tiltSharp, map_sum]
    simp only [hdw]
  have hsw : ∀ i, ‖tiltSharp C p (w i)‖ ≤ 1 := fun i => by rw [norm_tiltSharp]; exact hw1 i

  have haj : ‖algebraMap 𝒪K♭ K♭ (a j)‖ = ‖l j‖ := by
    rw [norm_algebraMap_preTilt, preTilt_norm_def]
    exact norm_eq_of_norm_sub_lt ((ha j).trans_lt hpl)
  have hAbig : t * r * ρ < ‖A‖ := by
    rw [hAn]
    refine lt_of_lt_of_le ?_ (hw _ j)
    rw [norm_smul, haj]
    have : ρ * r < ‖l j‖ * ‖w j‖ :=
      mul_lt_mul'' hj (hwr j) hρ.le hr
    nlinarith

  have hS : ‖∑ i, ((d i).untilt : C) - A‖ ≤ ‖(p : K)‖ := by
    rw [norm_sub_rev, hA, ← norm_natCast_algebra (C := C)]
    exact norm_untilt_sum_sub_le Finset.univ d
  have hT : ‖∑ i, l i • tiltSharp C p (w i) - ∑ i, ((d i).untilt : C)‖ ≤ ‖(p : K)‖ := by
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [hdu, Algebra.smul_def, ← sub_mul, ← map_sub, norm_mul, norm_algebraMap', norm_sub_rev]
    calc ‖((a i).untilt : K) - l i‖ * ‖tiltSharp C p (w i)‖ ≤ ‖(p : K)‖ * 1 := by
          gcongr
          · exact ha i
          · exact hsw i
      _ = _ := mul_one _
  have hE : ‖∑ i, l i • tiltSharp C p (w i) - A‖ ≤ ‖(p : K)‖ := by
    have e : ∑ i, l i • tiltSharp C p (w i) - A =
        (∑ i, l i • tiltSharp C p (w i) - ∑ i, ((d i).untilt : C)) +
          (∑ i, ((d i).untilt : C) - A) := by abel
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hT hS)
  rw [norm_eq_of_norm_sub_lt (hE.trans_lt (hp.trans_lt hAbig))]
  exact hAbig

theorem mul_norm_le_norm_sum_smul_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) (l : ι → K) (i : ι) :
    t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by
  by_cases hli : l i = 0
  · rw [hli, norm_zero, mul_zero]; exact norm_nonneg _
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => ‖l j‖)
    ⟨i, Finset.mem_univ i⟩
  set m := ‖l i0‖ with hm
  have hli0 : ‖l i‖ ≤ m := hi0 i (Finset.mem_univ i)
  have hm0 : 0 < m := (norm_pos_iff.2 hli).trans_le hli0
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc p (K := K) (div_pos hρ hm0)
    (div_lt_div_of_pos_right hρ1 hm0)
  have hc0 : 0 < ‖c‖ := (div_pos hρ hm0).trans hc1
  have hcm : ‖c‖ * m ≤ 1 := by rwa [le_div_iff₀ hm0] at hc2
  have hcm' : ρ < ‖c‖ * m := by rwa [div_lt_iff₀ hm0] at hc1
  have key := lt_norm_sum_smul_tiltSharp (C := C) hw hw1 hwr ht hr hρ hp
    (l := fun j => c * l j) (j := i0)
    (fun j => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ j)) (norm_nonneg c)).trans hcm)
    (by rw [norm_mul]; exact hcm')
  have e : ∑ j, (c * l j) • tiltSharp C p (w j) = c • ∑ j, l j • tiltSharp C p (w j) := by
    rw [Finset.smul_sum]; simp only [mul_smul]
  rw [e, norm_smul] at key
  have hX := norm_nonneg (∑ j, l j • tiltSharp C p (w j))
  have htrρ : 0 ≤ t * r * ρ := by positivity
  calc t * r * ρ * ‖l i‖ ≤ t * r * ρ * m := by gcongr
    _ ≤ ‖c‖ * ‖∑ j, l j • tiltSharp C p (w j)‖ * m := by gcongr
    _ = (‖c‖ * m) * ‖∑ j, l j • tiltSharp C p (w j)‖ := by ring
    _ ≤ 1 * ‖∑ j, l j • tiltSharp C p (w j)‖ := by gcongr
    _ = _ := one_mul _

theorem linearIndependent_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 < r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) :
    LinearIndependent K (fun i => tiltSharp C p (w i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := mul_norm_le_norm_sum_smul_tiltSharp (C := C) hw hw1 hwr ht hr.le hρ hρ1 hp g i
  rw [hg, norm_zero] at h
  have hpos : 0 < t * r * ρ := by positivity
  have : ‖g i‖ ≤ 0 := by nlinarith [norm_nonneg (g i)]
  exact norm_le_zero_iff.1 this

theorem exists_orthogonal_normalized {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) {t r : ℝ} (ht : t < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ w : ι → C♭, LinearIndependent K♭ w ∧ (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      ∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖ := by
  obtain ⟨w', hli, hspan, horth⟩ := exists_orthogonal_of_linearIndependent hv ht
  have hw'0 : ∀ i, 0 < ‖w' i‖ := fun i => norm_pos_iff.2 (hli.ne_zero i)
  have hE : ∀ i, ∃ e : K♭, r / ‖w' i‖ < ‖e‖ ∧ ‖e‖ ≤ 1 / ‖w' i‖ := fun i =>
    exists_norm_mem_Ioc p (div_pos hr0 (hw'0 i)) (div_lt_div_of_pos_right hr1 (hw'0 i))
  choose e he1 he2 using hE
  have he0 : ∀ i, e i ≠ 0 := fun i => norm_pos_iff.1 ((div_pos hr0 (hw'0 i)).trans (he1 i))
  have hsmul : ∀ c : ι → K♭, ∑ j, c j • (e j • w' j) = ∑ j, (c j * e j) • w' j := fun c => by
    simp only [mul_smul]
  refine ⟨fun i => e i • w' i, ?_, fun i => Submodule.smul_mem _ _ (hspan i), ?_, fun i => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [hsmul] at hg
    have := (Fintype.linearIndependent_iff.1 hli) _ hg i
    exact (mul_eq_zero.1 this).resolve_right (he0 i)
  · intro c i
    rw [hsmul, ← mul_smul]
    exact horth (fun j => c j * e j) i
  · rw [norm_smul]
    constructor
    · calc ‖e i‖ * ‖w' i‖ ≤ 1 / ‖w' i‖ * ‖w' i‖ := by gcongr; exact he2 i
        _ = 1 := one_div_mul_cancel (hw'0 i).ne'
    · calc r = r / ‖w' i‖ * ‖w' i‖ := (div_mul_cancel₀ r (hw'0 i).ne').symm
        _ < ‖e i‖ * ‖w' i‖ := mul_lt_mul_of_pos_right (he1 i) (hw'0 i)

theorem exists_tiltSharp_family {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ (w : ι → C♭) (t r ρ : ℝ), 0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧ 0 < ρ ∧ ρ < 1 ∧
      ‖(p : K)‖ ≤ t * r * ρ ∧ LinearIndependent K♭ w ∧
      (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      (∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖) ∧
      ∀ (l : ι → K) (i : ι), t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by
  obtain ⟨s, hs0, hs1, hs⟩ := exists_lt_mul_mul_lt_one (norm_nonneg (p : K))
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p))
  obtain ⟨w, hli, hspan, horth, hnorm⟩ := exists_orthogonal_normalized (K := K) (C := C) hv hs1 hs0 hs1
  exact ⟨w, s, s, s, hs0, hs1, hs0, hs1, hs0, hs1, hs.le, hli, hspan, horth, hnorm,
    mul_norm_le_norm_sum_smul_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2)
      hs0 hs0.le hs0 hs1 hs.le⟩

theorem exists_tiltSharp_linearIndependent {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ w : ι → C♭, (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧ (∀ i, ‖w i‖ ≤ 1) ∧
      LinearIndependent K♭ w ∧ LinearIndependent K (fun i => tiltSharp C p (w i)) := by
  obtain ⟨w, t, r, ρ, ht0, -, hr0, -, hρ0, hρ1, hp, hli, hspan, horth, hnorm, -⟩ :=
    exists_tiltSharp_family (K := K) (C := C) hv
  exact ⟨w, hspan, fun i => (hnorm i).1, hli,
    linearIndependent_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0 hρ0
      hρ1 hp⟩

end

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem exists_mul_eq_add_p_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    {ι : Type*} [Fintype ι] {w : ι → C♭} (hwN : ∀ i, w i ∈ N) (hw1 : ∀ i, ‖w i‖ ≤ 1)
    (hspan : ∀ x ∈ N, ∃ b : ι → K♭, x = ∑ i, b i • w i) {t r : ℝ} (ht : 0 < t)
    (hwr : ∀ i, r < ‖w i‖)
    (horth : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    {γ : 𝒪K♭} (hγ : ‖γ‖ ≤ t * r)
    {y : normInteger C} (hy : y ∈ untiltInteger K C p N) :
    ∃ v ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i)),
      ∃ y' ∈ untiltInteger K C p N,
        algebraMap K C ((PreTilt.untilt γ : normInteger K) : K) * (y : C) = v + (p : C) * y' := by
  classical
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i))
  obtain ⟨a, ha, z', hz', rfl⟩ := exists_eq_untilt_add_p_mul hy
  set x : C♭ := algebraMap 𝒪C♭ C♭ a with hx
  have hxN : x ∈ N := (mem_integerTilt N).1 ha
  have hx1 : ‖x‖ ≤ 1 := by
    rw [hx, norm_algebraMap_preTilt]; exact preTilt_norm_le_one a
  obtain ⟨b, hb⟩ := hspan x hxN

  set g : K♭ := algebraMap 𝒪K♭ K♭ γ with hg
  have hgn : ‖g‖ = ‖γ‖ := norm_algebraMap_preTilt γ
  have hcb : ∀ i, ‖g * b i‖ ≤ 1 := by
    intro i
    have h1 : t * ‖b i • w i‖ ≤ ‖x‖ := by rw [hb]; exact horth b i
    rw [norm_smul] at h1
    have h2 : t * (‖b i‖ * r) ≤ 1 := by
      calc t * (‖b i‖ * r) ≤ t * (‖b i‖ * ‖w i‖) := by
            gcongr; exact (hwr i).le
        _ ≤ ‖x‖ := h1
        _ ≤ 1 := hx1
    rw [norm_mul, hgn]
    calc ‖γ‖ * ‖b i‖ ≤ t * r * ‖b i‖ := by gcongr
      _ = t * (‖b i‖ * r) := by ring
      _ ≤ 1 := h2
  choose β hβ using fun i => (norm_le_one_iff_exists_algebraMap (K := K) (p := p)).1 (hcb i)
  choose ω hω using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hw1 i)

  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C)
  have hφ : ∀ e : 𝒪K♭, algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ e) = algebraMap 𝒪C♭ C♭ (φ e) :=
    fun e => tiltMap_algebraMap _ _ e
  have hφmem : ∀ e : 𝒪K♭, φ e ∈ integerTilt K C p N := fun e => by
    rw [mem_integerTilt, ← hφ]; exact N.algebraMap_mem _
  have hωmem : ∀ i, ω i ∈ integerTilt K C p N := fun i => by
    rw [mem_integerTilt, hω]; exact hwN i

  have hid : φ γ * a = ∑ i, φ (β i) * ω i := by
    apply IsFractionRing.injective 𝒪C♭ C♭
    rw [map_mul, ← hφ, map_sum]
    simp only [map_mul, ← hφ, hω, hβ]
    rw [← hx, hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hg]
    ring
  obtain ⟨z'', hz'', hsum⟩ := exists_untilt_sum_eq (N := N) Finset.univ
    (fun i => (⟨φ (β i) * ω i, mul_mem (hφmem _) (hωmem i)⟩ : integerTilt K C p N))
  refine ⟨∑ i, ((PreTilt.untilt (β i) : normInteger K) : K) • tiltSharp C p (w i),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    z'' + PreTilt.untilt (φ γ) * z', add_mem hz'' (mul_mem (untilt_mem_untiltInteger (hφmem γ)) hz'),
    ?_⟩
  have hsum' := congrArg (fun q : normInteger C => (q : C)) hsum
  simp only at hsum'
  have hγa : ((PreTilt.untilt (φ γ * a) : normInteger C) : C) =
      algebraMap K C ((PreTilt.untilt γ : normInteger K) : K) *
        ((PreTilt.untilt a : normInteger C) : C) := by
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap]
  rw [hid] at hγa
  have hterm : ∀ i, ((PreTilt.untilt (φ (β i) * ω i) : normInteger C) : C) =
      ((PreTilt.untilt (β i) : normInteger K) : K) • tiltSharp C p (w i) := by
    intro i
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap, Algebra.smul_def, ← hω,
      tiltSharp_algebraMap]
  rw [Subring.coe_add, Subring.coe_mul, mul_add, ← hγa, hsum']
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, AddSubmonoidClass.coe_finsetSum,
    hterm]
  rw [show ((PreTilt.untilt (φ γ) : normInteger C) : C) =
    algebraMap K C ((PreTilt.untilt γ : normInteger K) : K) from coe_untilt_preTiltMap _ _ γ]
  ring

theorem coe_mem_span_of_mem_untiltInteger (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    {ι : Type*} [Fintype ι] {w : ι → C♭} (hwN : ∀ i, w i ∈ N) (hw1 : ∀ i, ‖w i‖ ≤ 1)
    (hspan : ∀ x ∈ N, ∃ b : ι → K♭, x = ∑ i, b i • w i) {t r : ℝ} (ht : 0 < t)
    (hwr : ∀ i, r < ‖w i‖) (htr : t * r ≤ 1)
    (horth : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hp : ‖(p : K)‖ < t * r) {z : normInteger C} (hz : z ∈ untiltInteger K C p N) :
    (z : C) ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i)) := by
  classical
  have := IsPerfectoidField.completeSpace (K := K) p
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i)) with hVdef

  have htr0 : 0 < t * r := (norm_nonneg _).trans_lt hp
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc (K := K♭) p
    (lt_max_of_lt_right (half_pos htr0)) (max_lt hp (half_lt_self htr0))
  obtain ⟨γ, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 (hc2.trans htr)
  rw [norm_algebraMap_preTilt] at hc1 hc2
  have hpγ : ‖(p : K)‖ < ‖γ‖ := (le_max_left _ _).trans_lt hc1
  set e : K := ((PreTilt.untilt γ : normInteger K) : K) with he
  have hen : ‖e‖ = ‖γ‖ := (preTilt_norm_def γ).symm
  have he0 : e ≠ 0 := by
    intro h; rw [h, norm_zero] at hen; linarith [norm_nonneg (p : K)]
  set πK : K := (p : K) / e
  have hπ : ‖πK‖ < 1 := by
    rw [norm_div, hen, div_lt_one ((norm_nonneg _).trans_lt hpγ)]; exact hpγ
  set π : C := algebraMap K C πK

  have step : ∀ y : normInteger C, y ∈ untiltInteger K C p N →
      ∃ v ∈ V, ∃ y' ∈ untiltInteger K C p N, (y : C) = v + π * y' := by
    intro y hy
    obtain ⟨v, hv, y', hy', hyv⟩ := exists_mul_eq_add_p_mul N hwN hw1 hspan ht hwr horth hc2 hy
    refine ⟨e⁻¹ • v, V.smul_mem _ hv, y', hy', ?_⟩
    have hae : algebraMap K C e ≠ 0 := (map_ne_zero _).2 he0
    rw [Algebra.smul_def, map_inv₀]
    simp only [π, πK, map_div₀, map_natCast]
    field_simp
    rw [← he] at hyv
    linear_combination hyv

  have iter : ∀ k : ℕ, ∃ v ∈ V, ∃ y' ∈ untiltInteger K C p N, (z : C) = v + π ^ k * y' := by
    intro k
    induction k with
    | zero => exact ⟨0, V.zero_mem, z, hz, by simp⟩
    | succ k ih =>
      obtain ⟨v, hv, y, hy, hzv⟩ := ih
      obtain ⟨v', hv', y', hy', hyv⟩ := step y hy
      refine ⟨v + πK ^ k • v', V.add_mem hv (V.smul_mem _ hv'), y', hy', ?_⟩
      rw [hzv, hyv, Algebra.smul_def, map_pow]
      ring
  choose v hv y hy hzv using iter
  have hVc : IsClosed (V : Set C) := by
    have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
    exact V.closed_of_finiteDimensional
  have hlim : Filter.Tendsto v Filter.atTop (nhds (z : C)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ)
    have : v k - (z : C) = -(π ^ k * y k) := by rw [hzv k]; ring
    rw [this, norm_neg, norm_mul, norm_pow, norm_algebraMap']
    calc ‖πK‖ ^ k * ‖((y k : normInteger C) : C)‖ ≤ ‖πK‖ ^ k * 1 := by
          gcongr; exact mem_normInteger.1 (y k).2
      _ = _ := mul_one _
  exact hVc.mem_of_tendsto hlim (Filter.Eventually.of_forall hv)

theorem untiltField_le_of_subset (N : IntermediateField K♭ C♭) (V : Submodule K C)
    [FiniteDimensional K V] (hV : ∀ z ∈ untiltInteger K C p N, (z : C) ∈ V) :
    ∀ y ∈ untiltField K C p N, y ∈ V := by
  classical
  set S : Set C := (↑) '' (untiltInteger K C p N : Set (normInteger C))
  let T : Submonoid C :=
    { carrier := S
      one_mem' := ⟨1, (untiltInteger K C p N).one_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, (untiltInteger K C p N).mul_mem ha hb, rfl⟩ }
  have hA : Subalgebra.toSubmodule (Algebra.adjoin K S) ≤ V := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    have : x ∈ T := (Submonoid.closure_le (S := T)).2 le_rfl hx
    obtain ⟨z, hz, rfl⟩ := this
    exact hV z hz
  have : FiniteDimensional K (Algebra.adjoin K S) :=
    Submodule.finiteDimensional_of_le hA
  have halg : ∀ x ∈ S, IsAlgebraic K x := by
    intro x hx
    have hint : IsIntegral K (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin K S) :=
      Algebra.IsIntegral.isIntegral _
    exact (hint.map (Algebra.adjoin K S).val).isAlgebraic
  intro y hy
  have hy' : y ∈ (IntermediateField.adjoin K S).toSubalgebra := hy
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg] at hy'
  exact hA hy'

theorem exists_untiltField_basis (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    ∃ (w : Fin (Module.finrank K♭ N) → C♭) (t r ρ : ℝ), 0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧
      0 < ρ ∧ ρ < 1 ∧ ‖(p : K)‖ ≤ t * r * ρ ∧ (∀ i, w i ∈ N) ∧ (∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖) ∧
      (∀ x ∈ N, ∃ b : Fin (Module.finrank K♭ N) → K♭, x = ∑ i, b i • w i) ∧
      (∀ (c : Fin (Module.finrank K♭ N) → K♭) (i : Fin (Module.finrank K♭ N)),
        t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      (∀ (l : Fin (Module.finrank K♭ N) → K) (i : Fin (Module.finrank K♭ N)),
        t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖) ∧
      LinearIndependent K (fun i => tiltSharp C p (w i)) ∧
      (∀ y ∈ untiltField K C p N,
        y ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i))) := by
  classical
  set n := Module.finrank K♭ N
  set B := Module.finBasis K♭ N
  have hv : LinearIndependent K♭ (fun i => (B i : C♭)) :=
    B.linearIndependent.map' (IntermediateField.val N).toLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  obtain ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hli, hspanv, horth, hnorm, hest⟩ :=
    exists_tiltSharp_family (K := K) (C := C) hv
  have hwN : ∀ i, w i ∈ N := fun i => by
    have h := hspanv i
    have hle : Submodule.span K♭ (Set.range fun i => (B i : C♭)) ≤
        Subalgebra.toSubmodule N.toSubalgebra :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (B j).2)
    exact hle h

  let w' : Fin n → N := fun i => ⟨w i, hwN i⟩
  have hli' : LinearIndependent K♭ w' :=
    LinearIndependent.of_comp (IntermediateField.val N).toLinearMap hli
  have htop := hli'.span_eq_top_of_card_eq_finrank' (by simp [n])
  have hspan : ∀ x ∈ N, ∃ b : Fin n → K♭, x = ∑ i, b i • w i := by
    intro x hx
    have hmem : (⟨x, hx⟩ : N) ∈ Submodule.span K♭ (Set.range w') := by rw [htop]; trivial
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun K♭).1 hmem
    refine ⟨b, ?_⟩
    have := congrArg (fun u : N => (u : C♭)) hb
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, w'] at this
    exact this.symm
  have hptr : ‖(p : K)‖ < t * r := by
    calc ‖(p : K)‖ ≤ t * r * ρ := hp
      _ < t * r * 1 := by gcongr
      _ = t * r := mul_one _
  have htr : t * r ≤ 1 := by nlinarith
  have hsub : ∀ y ∈ untiltField K C p N,
      y ∈ Submodule.span K (Set.range fun i => tiltSharp C p (w i)) := by
    have : FiniteDimensional K (Submodule.span K (Set.range fun i => tiltSharp C p (w i))) :=
      FiniteDimensional.span_of_finite K (Set.finite_range _)
    exact untiltField_le_of_subset N _ fun z hz =>
      coe_mem_span_of_mem_untiltInteger N hwN (fun i => (hnorm i).1) hspan ht0
        (fun i => (hnorm i).2) htr horth hptr hz
  exact ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hwN, hnorm, hspan, horth, hest,
    linearIndependent_tiltSharp horth (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0 hρ0
      hρ1 hp, hsub⟩

instance finiteDimensional_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    FiniteDimensional K (untiltField K C p N) := by
  obtain ⟨w, t, r, ρ, -, -, -, -, -, -, -, hwN, -, -, -, -, hli, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i))
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  let f : untiltField K C p N →ₗ[K] V :=
    { toFun := fun y => ⟨y, hsub y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg Subtype.val h :)

theorem finrank_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    Module.finrank K (untiltField K C p N) = Module.finrank K♭ N := by
  obtain ⟨w, t, r, ρ, -, -, -, -, -, -, -, hwN, -, -, -, -, hli, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set V := Submodule.span K (Set.range fun i => tiltSharp C p (w i))
  have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
  apply le_antisymm
  · let f : untiltField K C p N →ₗ[K] V :=
      { toFun := fun y => ⟨y, hsub y y.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg Subtype.val h :)
    calc Module.finrank K (untiltField K C p N) ≤ Module.finrank K V :=
          LinearMap.finrank_le_finrank_of_injective hf
      _ ≤ Fintype.card (Fin (Module.finrank K♭ N)) := finrank_range_le_card _
      _ = _ := Fintype.card_fin _
  · let u : Fin (Module.finrank K♭ N) → untiltField K C p N :=
      fun i => ⟨tiltSharp C p (w i), tiltSharp_mem_untiltField (hwN i)⟩
    have hu : LinearIndependent K u :=
      LinearIndependent.of_comp (IntermediateField.val _).toLinearMap hli
    simpa using hu.fintype_card_le_finrank

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

section Norm

variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)

theorem surjective_pow_of_norm
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖) :
    Function.Surjective (fun x : ModP (normInteger F) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy1, hy⟩ := h x (mem_normInteger.1 x.2)
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  rw [Ideal.Quotient.eq]
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := (⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x) 1).2
  have hle : ‖(((⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x : normInteger F) : F)‖ ≤
      ‖((p : normInteger F) : F)‖ ^ 1 := by
    rw [pow_one, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, norm_sub_rev]
    simpa using hy
  have := hmem hle
  rwa [pow_one] at this

end Norm

section Perfectoid

private theorem norm_sub_le_max_of_ultrametric_field {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]

theorem exists_norm_sub_pow_le [IsPerfectoidField F p] {x : F} (hx : ‖x‖ ≤ 1) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
  obtain ⟨z, hz⟩ := IsPerfectoidField.surjective_pow (K := F) (p := p)
    (Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨y, mem_normInteger.1 y.2, ?_⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {(p : normInteger F)}) (⟨x, mem_normInteger.2 hx⟩ - y ^ p)
      = 0 := by
    rw [map_sub, map_pow]
    exact sub_eq_zero.2 hz.symm
  rw [Ideal.Quotient.eq_zero_iff_mem] at hz'
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := ⟨x, mem_normInteger.2 hx⟩ - y ^ p) 1).1 (by rwa [pow_one])
  simpa using hmem

theorem exists_norm_sub_pow_step {π : F} (hπ : ‖π‖ ≤ 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p)
    {x z : F} (hz : ‖z‖ ≤ 1) {k : ℕ} (hxz : ‖x - z ^ p‖ ≤ ‖π‖ ^ (p * k)) :
    ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ ‖π‖ ^ k ∧
      ‖x - z' ^ p‖ ≤ max (‖π‖ ^ (p * (k + 1))) (‖(p : F)‖ * ‖π‖ ^ k) := by
  have hp : p.Prime := Fact.out
  by_cases h0 : π ^ (p * k) = 0
  · refine ⟨z, hz, by simp [pow_nonneg (norm_nonneg π)], ?_⟩
    have : ‖x - z ^ p‖ ≤ 0 := by rwa [← norm_pow, h0, norm_zero] at hxz
    exact this.trans (le_max_of_le_left (pow_nonneg (norm_nonneg _) _))
  set w := (x - z ^ p) / π ^ (p * k) with hw
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_div, norm_pow]
    exact div_le_one_of_le₀ hxz (pow_nonneg (norm_nonneg _) _)
  obtain ⟨u, hu1, hu⟩ := h w hw1
  have hπk : ‖π ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ
  have hb1 : ‖π ^ k * u‖ ≤ 1 := by
    rw [norm_mul]; exact mul_le_one₀ hπk (norm_nonneg _) hu1
  refine ⟨z + π ^ k * u, ?_, ?_, ?_⟩
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz hb1)
  · rw [add_sub_cancel_left, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hu1
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨z, mem_normInteger.2 hz⟩ : normInteger F)
      ⟨π ^ k * u, mem_normInteger.2 hb1⟩
    have hr' := congrArg (fun t : normInteger F => (t : F)) hr
    simp only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul,
      SubringClass.coe_natCast] at hr'
    have hr1 : ‖(r : F)‖ ≤ 1 := mem_normInteger.1 r.2
    have hxw : x - z ^ p = π ^ (p * k) * w := by
      rw [hw, mul_div_cancel₀ _ h0]
    have key : x - (z + π ^ k * u) ^ p =
        π ^ (p * k) * (w - u ^ p) - (p : F) * z * (π ^ k * u) * r := by
      rw [hr']
      have : (π ^ k * u) ^ p = π ^ (p * k) * u ^ p := by
        rw [mul_pow, ← pow_mul, mul_comm k p]
      rw [this]
      linear_combination hxw
    rw [key]
    refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le_max ?_ ?_)
    · rw [norm_mul, norm_pow, mul_add, mul_one, pow_add]
      exact mul_le_mul_of_nonneg_left hu (pow_nonneg (norm_nonneg _) _)
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
      have h1 : ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ ‖π‖ ^ k := by
        calc ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ 1 * (‖π‖ ^ k * 1) * 1 := by
              gcongr
          _ = ‖π‖ ^ k := by ring
      calc ‖(p : F)‖ * ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖
          = ‖(p : F)‖ * (‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖) := by ring
        _ ≤ ‖(p : F)‖ * ‖π‖ ^ k := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem of_norm_sub_pow_le {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (hnd : ∀ r : ℝ, r < 1 → ∃ x : F, r < ‖x‖ ∧ ‖x‖ < 1) {π : F} (hπ : ‖π‖ < 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p) : IsPerfectoidField F p := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set c := ‖π‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _

  have key : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
    intro x hx
    by_cases hpz : (p : F) = 0
    ·
      have hstep : ∀ (k : ℕ) (z : F), ‖z‖ ≤ 1 → ‖x - z ^ p‖ ≤ c ^ (p * k) →
          ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ c ^ k ∧ ‖x - z' ^ p‖ ≤ c ^ (p * (k + 1)) := by
        intro k z hz hxz
        obtain ⟨z', h1, h2, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hxz
        refine ⟨z', h1, h2, h3.trans (max_le le_rfl ?_)⟩
        rw [hpz, norm_zero, zero_mul]
        exact pow_nonneg hc0 _
      let S : ℕ → Type _ := fun k => {z : F // ‖z‖ ≤ 1 ∧ ‖x - z ^ p‖ ≤ c ^ (p * k)}
      let next : (k : ℕ) → S k → S (k + 1) := fun k z =>
        ⟨Classical.choose (hstep k z.1 z.2.1 z.2.2),
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).1,
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.2⟩
      have hnext : ∀ (k : ℕ) (z : S k), ‖(next k z).1 - z.1‖ ≤ c ^ k := fun k z =>
        (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.1
      have base : ‖x - (0 : F) ^ p‖ ≤ c ^ (p * 0) := by
        rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
      let s : (k : ℕ) → S k := fun k => Nat.rec ⟨0, by simp, base⟩ next k
      let z : ℕ → F := fun k => (s k).1
      have hdist : ∀ k, dist (z k) (z (k + 1)) ≤ 1 * c ^ k := by
        intro k
        rw [one_mul, dist_comm, dist_eq_norm]
        exact hnext k (s k)
      have hcau : CauchySeq z := cauchySeq_of_le_geometric c 1 hπ hdist
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
      have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun k => (s k).2.1
      refine ⟨L, hL1, ?_⟩
      have ht0 : Filter.Tendsto (fun k => c ^ (p * k)) Filter.atTop (nhds 0) := by
        simp_rw [pow_mul]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hc0 _)
          (pow_lt_one₀ hc0 hπ hp0)
      have h1 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) (fun k => (s k).2.2) ht0
      have h2 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds ‖x - L ^ p‖) :=
        (tendsto_const_nhds.sub (hL.pow p)).norm
      rw [tendsto_nhds_unique h2 h1]
      exact norm_nonneg _
    ·
      have hpos : 0 < ‖(p : F)‖ := norm_pos_iff.2 hpz
      have hind : ∀ k : ℕ, ∃ z : F, ‖z‖ ≤ 1 ∧
          (‖x - z ^ p‖ ≤ ‖(p : F)‖ ∨ ‖x - z ^ p‖ ≤ c ^ (p * k)) := by
        intro k
        induction k with
        | zero =>
          refine ⟨0, by simp, Or.inr ?_⟩
          rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
        | succ k ih =>
          obtain ⟨z, hz, hz'⟩ := ih
          rcases hz' with hz' | hz'
          · exact ⟨z, hz, Or.inl hz'⟩
          · obtain ⟨z', h1, -, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hz'
            refine ⟨z', h1, ?_⟩
            rcases le_total (c ^ (p * (k + 1))) (‖(p : F)‖ * c ^ k) with hle | hle
            · left
              refine h3.trans ((max_eq_right hle).le.trans ?_)
              exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hc0 hπ.le)
            · right
              exact h3.trans (max_eq_left hle).le
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hπ
      obtain ⟨z, hz, hz'⟩ := hind n
      refine ⟨z, hz, hz'.elim id fun h' => h'.trans ?_⟩
      refine le_trans ?_ hn.le
      exact pow_le_pow_of_le_one hc0 hπ.le (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hp0))
  exact
    { complete := inferInstance
      norm_natCast_lt_one := hp
      exists_norm_mem_Ioo := hnd
      surjective_pow := surjective_pow_of_norm p key }

theorem of_ringEquiv {F F' : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [NontriviallyNormedField F'] [IsUltrametricDist F'] (p : ℕ) [Fact p.Prime]
    [IsPerfectoidField F p] (e : F ≃+* F') (he : ∀ x, ‖e x‖ = ‖x‖) : IsPerfectoidField F' p := by
  have := completeSpace (K := F) p
  have hiso : Isometry e := Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, he]
  let ie : F ≃ᵢ F' := { e.toEquiv with isometry_toFun := hiso }
  have he' : ∀ y, ‖e.symm y‖ = ‖y‖ := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rw [he]
  have hpF : ‖(p : F')‖ = ‖(p : F)‖ := by rw [← map_natCast e p, he]
  exact
    { complete := ie.symm.completeSpace
      norm_natCast_lt_one := hpF ▸ norm_natCast_lt_one (K := F) (p := p)
      exists_norm_mem_Ioo := fun r hr => by
        obtain ⟨x, h1, h2⟩ := exists_norm_mem_Ioo (K := F) (p := p) r hr
        exact ⟨e x, by rwa [he], by rwa [he]⟩
      surjective_pow := surjective_pow_of_norm p fun y hy => by
        obtain ⟨x, hx1, hx⟩ := exists_norm_sub_pow_le p (x := e.symm y) (by rwa [he'])
        refine ⟨e x, by rwa [he], ?_⟩
        have hyx : y - e x ^ p = e (e.symm y - x ^ p) := by
          rw [map_sub, map_pow, e.apply_symm_apply]
        rw [hpF, hyx, he]
        exact hx }

end Perfectoid

end IsPerfectoidField

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem exists_norm_sub_pow_le_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    ∃ πK : K, ‖πK‖ < 1 ∧ ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ q ∈ untiltField K C p N, ‖q‖ ≤ 1 ∧ ‖y - q ^ p‖ ≤ ‖πK‖ ^ p := by
  classical
  obtain ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hwN, hnorm, -, horth, -, -, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set ρ' := (1 + ρ) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := hρ0.trans hρρ'
  have htr : 0 < t * r := mul_pos ht0 hr0
  have hp' : ‖(p : K)‖ ≤ t * r * ρ' := hp.trans (by gcongr)
  have hpstrict : ‖(p : K)‖ < t * r * ρ' :=
    hp.trans_lt (mul_lt_mul_of_pos_left hρρ' htr)
  have hest := fun l i => mul_norm_le_norm_sum_smul_tiltSharp (K := K) (C := C) (p := p) horth
    (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0.le hρ'0 hρ'1 hp' l i
  set b := t * r * ρ' with hbdef
  have hb0 : 0 < b := mul_pos htr hρ'0
  have hb1 : b ≤ 1 := by
    have : t * r ≤ 1 := by nlinarith
    calc b = t * r * ρ' := rfl
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

  obtain ⟨ε, hε1, hε2⟩ := exists_norm_mem_Ioc (K := K♭) p
    (lt_max_of_lt_right (half_pos hb0)) (max_lt hpstrict (half_lt_self hb0))
  obtain ⟨γ, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 (hε2.trans hb1)
  rw [norm_algebraMap_preTilt] at hε1 hε2
  have hpγ : ‖(p : K)‖ < ‖γ‖ := (le_max_left _ _).trans_lt hε1
  set γ' := (frobeniusEquiv 𝒪K♭ p).symm γ
  set e : K := ((PreTilt.untilt γ : normInteger K) : K) with he
  set e' : K := ((PreTilt.untilt γ' : normInteger K) : K) with he'
  have hee' : e' ^ p = e := by
    rw [he', he, ← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hen : ‖e‖ = ‖γ‖ := (preTilt_norm_def γ).symm
  have he0 : 0 < ‖e‖ := hen ▸ (norm_nonneg _).trans_lt hpγ
  have he'0 : e' ≠ 0 := by
    intro h; rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hee'
    rw [← hee', norm_zero] at he0; exact lt_irrefl _ he0
  set base := ‖(p : K)‖ / ‖e‖ with hbase
  have hbase0 : 0 ≤ base := div_nonneg (norm_nonneg _) he0.le
  have hbase1 : base < 1 := by rw [hbase, div_lt_one he0, hen]; exact hpγ
  have hpn : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set r0 := base ^ ((p : ℝ)⁻¹) with hr0def
  have hr01 : r0 < 1 := Real.rpow_lt_one hbase0 hbase1 (inv_pos.2 (by positivity))
  obtain ⟨πK, hπ1, hπ2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r0 hr01
  refine ⟨πK, hπ2, fun y hyF hy1 => ?_⟩
  have hbaseπ : base ≤ ‖πK‖ ^ p := by
    have h1 : r0 ^ p = base := Real.rpow_inv_natCast_pow hbase0 (Fact.out : p.Prime).ne_zero
    rw [← h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hbase0 _) hπ1.le p

  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsub y hyF)
  have hlb : ∀ i, ‖e * l i‖ ≤ 1 := by
    intro i
    have h1 := hest l i
    rw [hl] at h1
    rw [norm_mul, hen]
    calc ‖γ‖ * ‖l i‖ ≤ b * ‖l i‖ := by gcongr
      _ ≤ ‖y‖ := h1
      _ ≤ 1 := hy1
  choose a ha using fun i => exists_mk_untilt_eq (p := p)
    (⟨e * l i, mem_normInteger.2 (hlb i)⟩ : normInteger K)
  have ha' : ∀ i, ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ ≤ ‖(p : K)‖ :=
    fun i => mk_eq_mk_iff_norm_sub_le.1 (ha i)
  choose ω hω using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hnorm i).1
  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C)
  have hφmem : ∀ c : 𝒪K♭, φ c ∈ integerTilt K C p N := fun c => by
    rw [mem_integerTilt]
    have : algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ c) = algebraMap 𝒪C♭ C♭ (φ c) :=
      tiltMap_algebraMap _ _ c
    rw [← this]; exact N.algebraMap_mem _
  have hωmem : ∀ i, ω i ∈ integerTilt K C p N := fun i => by
    rw [mem_integerTilt, hω]; exact hwN i
  set X : 𝒪C♭ := ∑ i, φ (a i) * ω i
  have hXmem : X ∈ integerTilt K C p N :=
    Subring.sum_mem _ fun i _ => mul_mem (hφmem _) (hωmem i)
  set X' := (frobeniusEquiv 𝒪C♭ p).symm X
  have hX'mem : X' ∈ integerTilt K C p N := frobeniusEquiv_symm_mem_integerTilt hXmem
  have hX'p : ((PreTilt.untilt X' : normInteger C) : C) ^ p = ((PreTilt.untilt X : normInteger C) : C) := by
    rw [← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  set q : C := ((PreTilt.untilt X' : normInteger C) : C) / algebraMap K C e'
  have hqF : q ∈ untiltField K C p N :=
    div_mem (coe_mem_untiltField (untilt_mem_untiltInteger hX'mem))
      (IntermediateField.algebraMap_mem _ _)
  have hqp : q ^ p = ((PreTilt.untilt X : normInteger C) : C) / algebraMap K C e := by
    rw [div_pow, hX'p, ← map_pow, hee']

  have hterm : ∀ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) =
      ((PreTilt.untilt (a i) : normInteger K) : K) • tiltSharp C p (w i) := by
    intro i
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap, Algebra.smul_def, ← hω,
      tiltSharp_algebraMap]
  have h1 : ‖algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤
      ‖(p : K)‖ := by
    have : algebraMap K C e * y -
        ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) =
        ∑ i, (e * l i - ((PreTilt.untilt (a i) : normInteger K) : K)) • tiltSharp C p (w i) := by
      rw [← hl, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      simp only [Algebra.smul_def, map_mul, map_sub]
      ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_smul, norm_tiltSharp, norm_sub_rev]
    calc ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ * ‖w i‖
        ≤ ‖(p : K)‖ * 1 := mul_le_mul (ha' i) (hnorm i).1 (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _
  have h2 : ‖((PreTilt.untilt X : normInteger C) : C) -
      ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
    rw [← norm_natCast_algebra (K := K) (C := C)]
    exact norm_untilt_sum_sub_le Finset.univ fun i => φ (a i) * ω i
  have h3 : ‖algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
    have : algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C) =
        (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) -
        (((PreTilt.untilt X : normInteger C) : C) -
          ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) := by ring
    rw [this]
    have := IsUltrametricDist.norm_add_le_max
      (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C))
      (-(((PreTilt.untilt X : normInteger C) : C) -
          ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)))
    rw [norm_neg, ← sub_eq_add_neg] at this
    exact this.trans (max_le h1 h2)
  have hae : algebraMap K C e ≠ 0 :=
    (map_ne_zero _).2 (fun h => by rw [h, norm_zero] at he0; exact lt_irrefl _ he0)
  have hyq : ‖y - q ^ p‖ ≤ base := by
    have : y - q ^ p = (algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)) /
        algebraMap K C e := by
      rw [hqp]; field_simp
    rw [this, norm_div, norm_algebraMap', hbase]
    exact div_le_div_of_nonneg_right h3 he0.le
  refine ⟨q, hqF, ?_, hyq.trans hbaseπ⟩
  have hqp1 : ‖q‖ ^ p ≤ 1 := by
    rw [← norm_pow]
    have : q ^ p = y - (y - q ^ p) := by ring
    rw [this]
    have := IsUltrametricDist.norm_add_le_max y (-(y - q ^ p))
    rw [norm_neg, ← sub_eq_add_neg] at this
    exact this.trans (max_le hy1 (hyq.trans hbase1.le))
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : p.Prime).ne_zero).1 hqp1

instance isPerfectoidField_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    IsPerfectoidField (untiltField K C p N) p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace (untiltField K C p N) := FiniteDimensional.complete K _
  obtain ⟨πK, hπ, h⟩ := exists_norm_sub_pow_le_untiltField (K := K) (C := C) (p := p) N
  refine IsPerfectoidField.of_norm_sub_pow_le p ?_ ?_ (π := algebraMap K _ πK) ?_ ?_
  · change ‖((p : untiltField K C p N) : C)‖ < 1
    rw [show ((p : untiltField K C p N) : C) = (p : C) from map_natCast (untiltField K C p N).val p,
      norm_natCast_algebra (K := K)]
    exact IsPerfectoidField.norm_natCast_lt_one
  · intro r hr
    obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
    refine ⟨algebraMap K _ x, ?_, ?_⟩ <;> rw [norm_algebraMap'] <;> assumption
  · rw [norm_algebraMap']; exact hπ
  · intro x hx
    obtain ⟨q, hqF, hq1, hq⟩ := h x x.2 hx
    refine ⟨⟨q, hqF⟩, hq1, ?_⟩
    rw [norm_algebraMap']
    exact hq

theorem iterate_frobeniusEquiv_symm_mem_integerTilt {N : IntermediateField K♭ C♭}
    [FiniteDimensional K♭ N] {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) (n : ℕ) :
    (frobeniusEquiv 𝒪C♭ p).symm^[n] a ∈ integerTilt K C p N := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact frobeniusEquiv_symm_mem_integerTilt ih

theorem le_tiltIntermediateField_untiltField (N : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ N] : N ≤ tiltIntermediateField p (untiltField K C p N) := by
  have key : ∀ z ∈ N, ‖z‖ ≤ 1 → z ∈ tiltIntermediateField p (untiltField K C p N) := by
    intro z hz hz1
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz1
    have ha : a ∈ integerTilt K C p N := (mem_integerTilt N).2 hz
    exact algebraMap_mem_tiltIntermediateField _ fun n =>
      coe_mem_untiltField (untilt_mem_untiltInteger (iterate_frobeniusEquiv_symm_mem_integerTilt ha n))
  intro z hz
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact key z hz h
  · have h0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h; linarith
    have := key z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    simpa using inv_mem this

theorem tiltIntermediateField_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    tiltIntermediateField p (untiltField K C p N) = N := by
  classical
  set T := tiltIntermediateField p (untiltField K C p N)
  have hle := le_tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N

  have hbound : ∀ s : Finset T, LinearIndependent K♭ (fun i : s => (i : T)) →
      s.card ≤ Module.finrank K (untiltField K C p N) := by
    intro s hs
    have hv : LinearIndependent K♭ (fun i : s => ((i : T) : C♭)) :=
      hs.map' T.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    obtain ⟨w, hw, -, -, hli⟩ := exists_tiltSharp_linearIndependent (K := K) (C := C) hv
    have hwT : ∀ i, w i ∈ T := fun i => by
      have hsp : Submodule.span K♭ (Set.range fun i : s => ((i : T) : C♭)) ≤
          Subalgebra.toSubmodule T.toSubalgebra :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ((j : T)).2)
      exact hsp (hw i)
    let u : s → untiltField K C p N := fun i =>
      ⟨tiltSharp C p (w i), tiltSharp_mem_of_mem_tiltIntermediateField _ (hwT i)⟩
    have hu : LinearIndependent K u :=
      LinearIndependent.of_comp (IntermediateField.val _).toLinearMap hli
    simpa using hu.fintype_card_le_finrank
  have hrank : Module.rank K♭ T ≤ Module.finrank K (untiltField K C p N) := rank_le hbound
  have hfin : FiniteDimensional K♭ T :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have hfr : Module.finrank K♭ T ≤ Module.finrank K♭ N := by
    rw [← finrank_untiltField (K := K) (C := C) (p := p) N]
    exact Module.finrank_le_of_rank_le hrank
  exact (IntermediateField.eq_of_le_of_finrank_le hle hfr).symm

theorem exists_norm_sub_untilt_le (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] {y : C}
    (hy : y ∈ untiltField K C p N) (hy1 : ‖y‖ ≤ 1) :
    ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
  set F := untiltField K C p N
  obtain ⟨b, hb⟩ := exists_mk_untilt_eq (K := F) (p := p) ⟨⟨y, hy⟩, mem_normInteger.2 hy1⟩
  rw [mk_eq_mk_iff_norm_sub_le] at hb
  set a := preTiltMap p (F.val : F →+* C) (norm_val F) b
  have hacoe : ((PreTilt.untilt a : normInteger C) : C) =
      (((PreTilt.untilt b : normInteger F) : F) : C) :=
    coe_untilt_preTiltMap _ _ b
  have haN : a ∈ integerTilt K C p N := by
    rw [mem_integerTilt, ← tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N]
    refine ⟨algebraMap _ _ b, ?_⟩
    rw [tiltInclusion, tiltMap_algebraMap]
  refine ⟨a, haN, ?_⟩
  rw [hacoe, norm_sub_rev]
  have hpF : ‖(p : F)‖ = ‖(p : K)‖ := by
    change ‖((p : F) : C)‖ = _
    rw [show ((p : F) : C) = (p : C) from map_natCast F.val p, norm_natCast_algebra (K := K)]
  rw [← hpF]
  exact hb

end GroundTheory.PAdicHodge
end
end
