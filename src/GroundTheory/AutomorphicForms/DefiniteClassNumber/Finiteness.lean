import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.AdelicLattice

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Submodule
open scoped RealInnerProductSpace

universe u

section Dual

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def latticeDual (L : AddSubgroup X) : AddSubgroup X where
  carrier := {y | ∀ x ∈ L, ∃ n : ℤ, ⟪y, x⟫ = n}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := fun {a b} ha hb x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨m + n, by rw [inner_add_left, hm, hn]; push_cast; ring⟩
  neg_mem' := fun {a} ha x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    exact ⟨-m, by rw [inner_neg_left, hm]; push_cast; ring⟩


theorem eq_zero_of_forall_inner_eq_zero {s : Set X} (hs : span ℝ s = ⊤) {y : X}
    (hy : ∀ x ∈ s, ⟪y, x⟫ = 0) : y = 0 := by
  have hle : span ℝ s ≤ LinearMap.ker (innerSL ℝ y).toLinearMap :=
    span_le.2 fun x hx => by simpa using hy x hx
  have hy' : y ∈ LinearMap.ker (innerSL ℝ y).toLinearMap := hle (hs ▸ mem_top)
  simpa using hy'

theorem finite_latticeDual_norm_le [FiniteDimensional ℝ X] {L : AddSubgroup X}
    (hL : span ℝ (L : Set X) = ⊤) (C : ℝ) :
    ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} : Set X).Finite := by
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent ℝ (L : Set X)
  rw [hL] at hspan
  have hsfin : s.Finite := hli.setFinite
  have : Finite s := hsfin.to_subtype
  let Φ : X → s → ℝ := fun y x => ⟪y, (x : X)⟫
  have hinj : Set.InjOn Φ {y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} := by
    intro y _ y' _ h
    have : y - y' = 0 := eq_zero_of_forall_inner_eq_zero hspan fun x hx => by
      have := congrFun h ⟨x, hx⟩
      simp only [Φ] at this
      rw [inner_sub_left, this, sub_self]
    exact sub_eq_zero.1 this
  refine Set.Finite.of_finite_image (Set.Finite.subset (Set.Finite.pi (t := fun x : s =>
    (Int.cast '' Set.Icc (-⌈C * ‖(x : X)‖⌉) ⌈C * ‖(x : X)‖⌉ : Set ℝ))
    fun x => (Set.finite_Icc _ _).image _) ?_) hinj
  rintro _ ⟨y, ⟨hyD, hyC⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro x
  obtain ⟨n, hn⟩ := hyD x (hsL x.2)
  refine ⟨n, ⟨?_, ?_⟩, hn.symm⟩
  all_goals
    have h1 : |(n : ℝ)| ≤ C * ‖(x : X)‖ := by
      rw [← hn]
      exact (abs_real_inner_le_norm y x).trans
        (mul_le_mul_of_nonneg_right hyC (norm_nonneg _))
    have h2 : C * ‖(x : X)‖ ≤ ⌈C * ‖(x : X)‖⌉ := Int.le_ceil _
  · have : -((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) ≤ n := by linarith [neg_abs_le (n : ℝ)]
    exact_mod_cast this
  · have : (n : ℝ) ≤ ((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) := by linarith [le_abs_self (n : ℝ)]
    exact_mod_cast this

end Dual

def shortBasisBound : ℕ → ℝ → ℝ
  | 0, _ => 0
  | N + 1, μ => N * shortBasisBound N (Real.sqrt 3 / 2 * μ) + μ⁻¹

theorem shortBasisBound_nonneg : ∀ (N : ℕ) {μ : ℝ}, 0 < μ → 0 ≤ shortBasisBound N μ
  | 0, _, _ => le_rfl
  | N + 1, μ, hμ => by
    have h3 : 0 < Real.sqrt 3 / 2 * μ := by positivity
    have := shortBasisBound_nonneg N h3
    simp only [shortBasisBound]
    positivity

section Reduction

theorem exists_short_basis (N : ℕ) : ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X], finrank ℝ X = N → ∀ (L : AddSubgroup X) (μ : ℝ), 0 < μ →
    span ℝ (L : Set X) = ⊤ → span ℝ (latticeDual L : Set X) = ⊤ →
    (∀ y ∈ latticeDual L, y ≠ 0 → μ ≤ ‖y‖) →
    ∃ e : Fin N → X, LinearIndependent ℝ e ∧ ∀ i, e i ∈ L ∧ ‖e i‖ ≤ shortBasisBound N μ := by
  induction N with
  | zero =>
    intro X _ _ _ _ L μ _ _ _ _
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ N ih =>
    intro X _ _ _ hdim L μ hμ hLspan hDspan hmin
    classical
    have : Nontrivial X := nontrivial_of_finrank_eq_succ hdim

    obtain ⟨y0, hy0, hy0ne⟩ : ∃ y ∈ latticeDual L, y ≠ 0 := by
      by_contra h
      push Not at h
      have hsub : (latticeDual L : Set X) ⊆ {0} := fun y hy => h y hy
      have hle := span_mono (R := ℝ) hsub
      rw [hDspan, span_singleton_eq_bot.2 rfl] at hle
      exact top_ne_bot (eq_bot_iff.2 hle)

    obtain ⟨w, ⟨⟨hwD, -⟩, hw0⟩, hwmin⟩ := Set.exists_min_image
      ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ ‖y0‖} ∩ {y | y ≠ 0}) (fun y => ‖y‖)
      ((finite_latticeDual_norm_le hLspan ‖y0‖).subset Set.inter_subset_left)
      ⟨y0, ⟨hy0, le_rfl⟩, hy0ne⟩
    have hwmin' : ∀ y ∈ latticeDual L, y ≠ 0 → ‖w‖ ≤ ‖y‖ := by
      intro y hy hyne
      by_cases h : ‖y‖ ≤ ‖y0‖
      · exact hwmin y ⟨⟨hy, h⟩, hyne⟩
      · exact (hwmin y0 ⟨⟨hy0, le_rfl⟩, hy0ne⟩).trans (le_of_not_ge h)
    have hwμ : μ ≤ ‖w‖ := hmin w hwD hw0
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0

    have hx1 : ∃ x ∈ L, ⟪w, x⟫ ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (eq_zero_of_forall_inner_eq_zero hLspan h)
    have hex : ∃ n : ℕ, 0 < n ∧ ∃ x ∈ L, ⟪w, x⟫ = n := by
      obtain ⟨x1, hx1L, hx1⟩ := hx1
      obtain ⟨m, hm⟩ := hwD x1 hx1L
      have hm0 : m ≠ 0 := by rintro rfl; exact hx1 (by simpa using hm)
      rcases lt_or_gt_of_ne hm0 with hneg | hpos
      · refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, -x1, neg_mem hx1L, ?_⟩
        rw [inner_neg_right, hm, Nat.cast_natAbs, Int.cast_abs,
          abs_of_neg (by exact_mod_cast hneg)]
      · refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, x1, hx1L, ?_⟩
        rw [hm, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    obtain ⟨hn0pos, x0, hx0L, hx0⟩ := Nat.find_spec hex
    have hdiv : ∀ x ∈ L, ∃ q : ℤ, ⟪w, x⟫ = q * (Nat.find hex : ℝ) := by
      intro x hx
      obtain ⟨m, hm⟩ := hwD x hx
      set n0 := Nat.find hex
      have hn0z : (0 : ℤ) < n0 := by exact_mod_cast hn0pos
      set r := m % (n0 : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ hn0z.ne'
      have hrlt : r < n0 := Int.emod_lt_of_pos _ hn0z
      have hmr : m = r + n0 * (m / n0) := (Int.emod_add_mul_ediv m n0).symm
      have hxr : x - (m / (n0 : ℤ)) • x0 ∈ L := sub_mem hx (zsmul_mem hx0L _)
      have hval : ⟪w, x - (m / (n0 : ℤ)) • x0⟫ = r := by
        rw [inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hm, hx0]
        have : (m : ℝ) = r + n0 * (m / (n0 : ℤ) : ℤ) := by exact_mod_cast hmr
        rw [this]; ring
      have hr : r = 0 := by
        by_contra hrne
        have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
        have := Nat.find_min hex (m := r.toNat) (by omega)
        apply this
        refine ⟨by omega, _, hxr, ?_⟩
        rw [hval]
        have : ((r.toNat : ℤ) : ℝ) = r := by rw [Int.toNat_of_nonneg hr0]
        rw [← this]; norm_cast
      refine ⟨m / n0, ?_⟩
      have hm' : m = (m / n0) * n0 := by rw [hr] at hmr; linarith
      rw [hm]
      exact_mod_cast hm'
    have hn0 : Nat.find hex = 1 := by
      by_contra hne
      have hge : (2 : ℝ) ≤ Nat.find hex := by
        have : 2 ≤ Nat.find hex := by omega
        exact_mod_cast this
      set n0 := Nat.find hex
      have hw'D : (n0 : ℝ)⁻¹ • w ∈ latticeDual L := by
        intro x hx
        obtain ⟨q, hq⟩ := hdiv x hx
        refine ⟨q, ?_⟩
        rw [real_inner_smul_left, hq]
        field_simp
      have hw'0 : (n0 : ℝ)⁻¹ • w ≠ 0 := smul_ne_zero (inv_ne_zero (by linarith)) hw0
      have h1 := hwmin' _ hw'D hw'0
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)] at h1
      have : (n0 : ℝ)⁻¹ * ‖w‖ < ‖w‖ := by
        have : (n0 : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; gcongr
        nlinarith
      linarith
    rw [hn0, Nat.cast_one] at hx0

    have : Fact (finrank ℝ X = N + 1) := ⟨hdim⟩
    set W : Submodule ℝ X := (ℝ ∙ w)ᗮ with hWdef
    have hWdim : finrank ℝ W = N := finrank_orthogonal_span_singleton hw0
    have memW : ∀ z : X, z ∈ W ↔ ⟪w, z⟫ = 0 := fun z => mem_orthogonal_singleton_iff_inner_right
    let M : AddSubgroup W := L.comap W.subtype.toAddMonoidHom
    have memM : ∀ m : W, m ∈ M ↔ (m : X) ∈ L := fun m => Iff.rfl

    let P : X →ₗ[ℝ] W :=
      { toFun := fun x => ⟨x - ⟪w, x⟫ • x0, by
          rw [memW, inner_sub_right, real_inner_smul_right, hx0]; ring⟩
        map_add' := fun x y => by
          ext; simp only [inner_add_right, add_smul, coe_add]; abel
        map_smul' := fun c x => by
          ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_smul] }
    have hP : ∀ x, (P x : X) = x - ⟪w, x⟫ • x0 := fun _ => rfl
    have hPL : ∀ x ∈ L, P x ∈ M := by
      intro x hx
      obtain ⟨n, hn⟩ := hwD x hx
      rw [memM, hP, hn, Int.cast_smul_eq_zsmul]
      exact sub_mem hx (zsmul_mem hx0L _)
    have hPW : ∀ z : W, P z = z := by
      intro z
      ext
      rw [hP, (memW z).1 z.2, zero_smul, sub_zero]
    have hPsurj : LinearMap.range P = ⊤ := LinearMap.range_eq_top.2 fun z => ⟨z, hPW z⟩
    have hMspan : span ℝ (M : Set W) = ⊤ := by
      apply eq_top_iff.2
      rw [← hPsurj, LinearMap.range_eq_map, ← hLspan, ← span_image]
      exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hPL x hx)

    let π : X →ₗ[ℝ] W :=
      { toFun := fun z => ⟨z - (⟪w, z⟫ / ‖w‖ ^ 2) • w, by
          rw [memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp; ring⟩
        map_add' := fun x y => by
          ext; simp only [inner_add_right, add_div, add_smul, coe_add]; abel
        map_smul' := fun c x => by
          ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_div_assoc,
            mul_smul] }
    have hπ : ∀ z, (π z : X) = z - (⟪w, z⟫ / ‖w‖ ^ 2) • w := fun _ => rfl
    have hπW : ∀ z : W, π z = z := by
      intro z
      ext
      rw [hπ, (memW z).1 z.2, zero_div, zero_smul, sub_zero]
    have hπD : ∀ z ∈ latticeDual L, π z ∈ latticeDual M := by
      intro z hz m hm
      obtain ⟨n, hn⟩ := hz m hm
      refine ⟨n, ?_⟩
      rw [coe_inner, hπ, inner_sub_left, real_inner_smul_left, (memW m).1 m.2, mul_zero, sub_zero, hn]
    have hMDspan : span ℝ (latticeDual M : Set W) = ⊤ := by
      apply eq_top_iff.2
      have hπsurj : LinearMap.range π = ⊤ := LinearMap.range_eq_top.2 fun z => ⟨z, hπW z⟩
      rw [← hπsurj, LinearMap.range_eq_map, ← hDspan, ← span_image]
      exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hπD x hx)

    have hMmin : ∀ y ∈ latticeDual M, y ≠ 0 → Real.sqrt 3 / 2 * μ ≤ ‖y‖ := by
      intro y hy hyne
      have hyw : ⟪(y : X), w⟫ = 0 := by rw [real_inner_comm]; exact (memW y).1 y.2
      set c := ⟪(y : X), x0⟫
      set s : ℝ := (round c : ℝ) - c
      have hs : |s| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round c
      set z := (y : X) + s • w
      have hzD : z ∈ latticeDual L := by
        intro x hx
        obtain ⟨n, hn⟩ := hwD x hx
        obtain ⟨k, hk⟩ := hy (P x) (hPL x hx)
        refine ⟨k + round c * n, ?_⟩
        rw [coe_inner, hP, inner_sub_right, real_inner_smul_right, hn] at hk
        rw [inner_add_left, real_inner_smul_left, hn]
        push_cast
        simp only [s]
        linear_combination hk
      have hz0 : z ≠ 0 := by
        intro h
        have : ⟪(y : X), z⟫ = ‖(y : X)‖ ^ 2 := by
          rw [inner_add_right, real_inner_smul_right, hyw, mul_zero, add_zero,
            real_inner_self_eq_norm_sq]
        rw [h, inner_zero_right] at this
        have hy0 : (y : X) = 0 := by
          have : ‖(y : X)‖ = 0 := by nlinarith [norm_nonneg (y : X)]
          exact norm_eq_zero.1 this
        exact hyne (Subtype.ext hy0)
      have hz := hwmin' z hzD hz0
      have hzn : ‖z‖ ^ 2 = ‖(y : X)‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, hyw, norm_smul, Real.norm_eq_abs, mul_pow,
          sq_abs]
        ring
      have hs2 : s ^ 2 ≤ 1 / 4 := by
        have := abs_le.1 hs
        nlinarith
      have hsq : (Real.sqrt 3 / 2 * μ) ^ 2 ≤ ‖y‖ ^ 2 := by
        have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have hw2 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
        have hμ2 : μ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hμ.le hwμ 2
        have : ‖y‖ = ‖(y : X)‖ := rfl
        rw [mul_pow, div_pow, h3, this]
        nlinarith
      exact le_of_sq_le_sq (by simpa using hsq) (norm_nonneg _) |>.trans_eq' rfl

    obtain ⟨e', hli', he'⟩ := ih (X := W) hWdim M (Real.sqrt 3 / 2 * μ) (by positivity) hMspan
      hMDspan hMmin
    set R' := shortBasisBound N (Real.sqrt 3 / 2 * μ)
    have hR' : 0 ≤ R' := shortBasisBound_nonneg N (by positivity)
    have hspan' : ⊤ ≤ span ℝ (Set.range e') := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        have : Subsingleton W := finrank_zero_iff.1 hWdim
        intro z _
        rw [Subsingleton.elim z 0]; exact zero_mem _
      · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
        exact (hli'.span_eq_top_of_card_eq_finrank (by simp [hWdim])).ge
    let B := Basis.mk hli' hspan'

    set q : W := ⟨x0 - (‖w‖ ^ 2)⁻¹ • w, by
      rw [memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx0]
      field_simp; ring⟩
    set c := B.repr q
    set x0' := x0 - ∑ i, ⌊c i⌋ • (e' i : X)
    have hx0'L : x0' ∈ L := sub_mem hx0L (sum_mem fun i _ => zsmul_mem (he' i).1 _)
    have hq : (q : X) = ∑ i, c i • (e' i : X) := by
      conv_lhs => rw [← B.sum_repr q]
      rw [coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coe_smul, Basis.mk_apply]
    have hx0'eq : x0' = ∑ i, Int.fract (c i) • (e' i : X) + (‖w‖ ^ 2)⁻¹ • w := by
      have hx0q : x0 = (q : X) + (‖w‖ ^ 2)⁻¹ • w := by simp [q]
      simp only [x0']
      rw [hx0q, hq]
      have : ∀ i, Int.fract (c i) • (e' i : X) = c i • (e' i : X) - ⌊c i⌋ • (e' i : X) := by
        intro i
        rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
      simp only [this, Finset.sum_sub_distrib]
      abel
    have hx0'norm : ‖x0'‖ ≤ N * R' + μ⁻¹ := by
      rw [hx0'eq]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans ?_
        have : ∀ i, ‖Int.fract (c i) • (e' i : X)‖ ≤ R' := by
          intro i
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
          have h1 := (he' i).2
          have h2 := (Int.fract_lt_one (c i)).le
          have : ‖(e' i : X)‖ = ‖e' i‖ := rfl
          rw [this]
          nlinarith [norm_nonneg (e' i), Int.fract_nonneg (c i)]
        refine (Finset.sum_le_sum fun i _ => this i).trans ?_
        simp
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), sq, mul_inv, mul_assoc,
          inv_mul_cancel₀ hwpos.ne', mul_one]
        exact inv_anti₀ hμ hwμ
    have hx0'w : ⟪w, x0'⟫ = 1 := by
      simp only [x0', inner_sub_right, inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
      rw [hx0]
      have : ∀ i, ⟪w, (e' i : X)⟫ = 0 := fun i => (memW _).1 (e' i).2
      simp [this]
    refine ⟨Fin.cons x0' fun i => (e' i : X), ?_, ?_⟩
    · rw [linearIndependent_finCons]
      refine ⟨hli'.map' W.subtype (ker_subtype W), ?_⟩
      intro hmem
      have hle : span ℝ (Set.range fun i => (e' i : X)) ≤ W :=
        span_le.2 (by rintro _ ⟨i, rfl⟩; exact (e' i).2)
      have := (memW _).1 (hle hmem)
      rw [hx0'w] at this
      exact one_ne_zero this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hx0'L, by simpa [shortBasisBound] using hx0'norm⟩
      · refine ⟨(he' j).1, ?_⟩
        simp only [Fin.cons_succ, shortBasisBound]
        have h1 : ‖(e' j : X)‖ ≤ R' := (he' j).2
        have hN1 : (1 : ℝ) ≤ N := by
          have : 0 < N := Fin.pos j
          exact_mod_cast this
        have : R' ≤ N * R' := le_mul_of_one_le_left hR' hN1
        have : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ.le
        linarith

end Reduction

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix Submodule
open scoped RealInnerProductSpace

variable {J : Type*} [Fintype J]

def GramSpace (_G : Matrix J J ℝ) : Type _ := J → ℝ

instance (G : Matrix J J ℝ) : AddCommGroup (GramSpace G) := inferInstanceAs (AddCommGroup (J → ℝ))

instance (G : Matrix J J ℝ) : Module ℝ (GramSpace G) := inferInstanceAs (Module ℝ (J → ℝ))

instance (G : Matrix J J ℝ) : FiniteDimensional ℝ (GramSpace G) :=
  inferInstanceAs (FiniteDimensional ℝ (J → ℝ))

def toGram (G : Matrix J J ℝ) : (J → ℝ) ≃ₗ[ℝ] GramSpace G := LinearEquiv.refl ℝ (J → ℝ)

@[instance_reducible]
def gramCore (G : Matrix J J ℝ) (hs : Gᵀ = G) (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) :
    InnerProductSpace.Core ℝ (GramSpace G) where
  inner x y := (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
  conj_inner_symm x y := by
    show (toGram G).symm y ⬝ᵥ (G *ᵥ (toGram G).symm x) = (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]
  re_inner_nonneg x := by
    show 0 ≤ (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm x)
    by_cases hx : (toGram G).symm x = 0
    · rw [hx]; simp
    · exact (hpos _ hx).le
  add_left x y z := by
    show (toGram G).symm (x + y) ⬝ᵥ _ = (toGram G).symm x ⬝ᵥ _ + (toGram G).symm y ⬝ᵥ _
    rw [map_add, add_dotProduct]
  smul_left x y r := by
    show (toGram G).symm (r • x) ⬝ᵥ _ = r * ((toGram G).symm x ⬝ᵥ _)
    rw [map_smul, smul_dotProduct, smul_eq_mul]
  definite x hx := by
    by_contra h
    have h' : (toGram G).symm x ≠ 0 := by simpa using h
    have := hpos _ h'
    exact (ne_of_gt this) hx



end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

variable (K) in

abbrev IntBasisIdx := Free.ChooseBasisIndex ℤ (𝓞 K)

def ratCoords (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℚ :=
  fun j => (integralBasis K).repr (vecCoords K b x j.1) j.2

def ofRatCoords (c : (ι × κ) × IntBasisIdx K → ℚ) : ι → K ⊗[K] E :=
  vecOfCoords b K fun a => (integralBasis K).equivFun.symm fun t => c (a, t)

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem ratCoords_ofRatCoords (c : (ι × κ) × IntBasisIdx K → ℚ) :
    ratCoords b (ofRatCoords b c) = c := by
  funext j
  simp only [ratCoords, ofRatCoords, vecCoords_vecOfCoords]
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem ofRatCoords_ratCoords (x : ι → K ⊗[K] E) : ofRatCoords b (ratCoords b x) = x := by
  conv_rhs => rw [← vecOfCoords_vecCoords b K x]
  simp only [ofRatCoords, ratCoords]
  congr 1
  funext a
  exact (integralBasis K).equivFun.symm_apply_apply (vecCoords K b x a)

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem ratCoords_injective : Function.Injective (ratCoords (ι := ι) b) := fun x y h => by
  rw [← ofRatCoords_ratCoords b x, h, ofRatCoords_ratCoords]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem ratCoords_add (x y : ι → K ⊗[K] E) :
    ratCoords b (x + y) = ratCoords b x + ratCoords b y := by
  funext j
  simp [ratCoords, vecCoords_add]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem ratCoords_zero : ratCoords b (0 : ι → K ⊗[K] E) = 0 := by
  funext j
  simp [ratCoords, vecCoords_zero]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem ratCoords_smul (q : ℚ) (x : ι → K ⊗[K] E) :
    ratCoords b ((q : K) • x) = q • ratCoords b x := by
  funext j
  simp only [ratCoords, vecCoords_smul, Pi.smul_apply]
  rw [← Rat.smul_def, map_smul]
  rfl

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem ratCoords_intSmul (m : ℤ) (x : ι → K ⊗[K] E) :
    ratCoords b ((m : K) • x) = (m : ℚ) • ratCoords b x := by
  rw [← ratCoords_smul, Rat.cast_intCast]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem ratCoords_sum {ι' : Type*} {s : Finset ι'} (x : ι' → ι → K ⊗[K] E) :
    ratCoords b (∑ i ∈ s, x i) = ∑ i ∈ s, ratCoords b (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ratCoords_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratCoords_add, ih]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] in

theorem isIntegral_vecCoords_ofRatCoords_single [DecidableEq κ] (j : (ι × κ) × IntBasisIdx K)
    (a : ι × κ) : IsIntegral ℤ (vecCoords K b (ofRatCoords b (Pi.single j 1)) a) := by
  classical
  simp only [ofRatCoords, vecCoords_vecOfCoords, Basis.equivFun_symm_apply]
  refine IsIntegral.sum _ fun t _ => ?_
  rw [Pi.single_apply]
  split_ifs
  · rw [one_smul, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  · rw [zero_smul]
    exact isIntegral_zero

variable (H : Matrix ι ι E)

def ratForm (θ : K) (x y : ι → K ⊗[K] E) : ℚ := Algebra.trace ℚ K (θ * hermTrace K H K x y)

variable {H}

omit [DecidableEq ι] in
theorem ratForm_add_left (θ : K) (x x' y : ι → K ⊗[K] E) :
    ratForm H θ (x + x') y = ratForm H θ x y + ratForm H θ x' y := by
  simp [ratForm, hermTrace_add_left, mul_add]

omit [DecidableEq ι] in
theorem ratForm_add_right (θ : K) (x y y' : ι → K ⊗[K] E) :
    ratForm H θ x (y + y') = ratForm H θ x y + ratForm H θ x y' := by
  simp [ratForm, hermTrace_add_right, mul_add]

omit [DecidableEq ι] in
theorem ratForm_smul_left (θ : K) (c : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ (c • x) y = Algebra.trace ℚ K (c * θ * hermTrace K H K x y) := by
  simp only [ratForm, hermTrace_smul_left]
  ring_nf

omit [DecidableEq ι] in
theorem ratForm_smul_right (θ : K) (c : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ x (c • y) = Algebra.trace ℚ K (c * θ * hermTrace K H K x y) := by
  simp only [ratForm, hermTrace_smul_right]
  ring_nf

omit [DecidableEq ι] in
theorem ratForm_ratSmul_left (θ : K) (q : ℚ) (x y : ι → K ⊗[K] E) :
    ratForm H θ ((q : K) • x) y = q * ratForm H θ x y := by
  rw [ratForm_smul_left, mul_assoc, ← Rat.smul_def, map_smul, smul_eq_mul]
  rfl

omit [DecidableEq ι] in
theorem ratForm_ratSmul_right (θ : K) (q : ℚ) (x y : ι → K ⊗[K] E) :
    ratForm H θ x ((q : K) • y) = q * ratForm H θ x y := by
  rw [ratForm_smul_right, mul_assoc, ← Rat.smul_def, map_smul, smul_eq_mul]
  rfl

omit [DecidableEq ι] in
theorem ratForm_comm (hH : IsHermitianFor (conjHom K E) H) (θ : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ y x = ratForm H θ x y := by
  rw [ratForm, ratForm, hermTrace_comm hH]

variable (H) in

theorem ratForm_eq (θ : K) (x y : ι → K ⊗[K] E) :
    ratForm H θ x y = ratCoords b x ⬝ᵥ (ratGram H b θ *ᵥ ratCoords b y) := by
  set ω := integralBasis K
  have hv : ∀ (z : ι → K ⊗[K] E) (a : ι × κ),
      vecCoords K b z a = ∑ t, (ratCoords b z (a, t) : K) * ω t := by
    intro z a
    conv_lhs => rw [← ω.sum_repr (vecCoords K b z a)]
    simp only [Rat.smul_def]
    rfl
  have swap4 : ∀ F : ι × κ → IntBasisIdx K → ι × κ → IntBasisIdx K → K,
      ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t' :=
    fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have key : θ * hermTrace K H K x y = ∑ j, ∑ j', ((ratCoords b x j * ratCoords b y j' : ℚ) : K) *
      (θ * ω j.2 * ω j'.2 * traceGram H b j.1 j'.1) := by
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hv, Finset.mul_sum, Finset.sum_mul]
    simp only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := IntBasisIdx K)]
    have swap2 : ∀ F : IntBasisIdx K → IntBasisIdx K → K,
        ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t' := fun F => Finset.sum_comm
    rw [swap4]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [swap2]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    push_cast
    ring
  rw [ratForm, key, map_sum]
  simp only [dotProduct, mulVec, ratGram, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [← Rat.smul_def, map_smul, smul_eq_mul]
  ring

def ratEmb (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℝ := fun j => (ratCoords b x j : ℝ)

variable (H) in
theorem ratEmb_gram (θ : K) (x y : ι → K ⊗[K] E) :
    ratEmb b x ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ ratEmb b y) = (ratForm H θ x y : ℝ) := by
  rw [ratForm_eq b H]
  simp only [ratEmb, dotProduct, mulVec, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul]

variable (H) in

def ratEmbHom : (ι → K ⊗[K] E) →+ ((ι × κ) × IntBasisIdx K → ℝ) where
  toFun := ratEmb b
  map_zero' := by funext j; simp [ratEmb, ratCoords_zero]
  map_add' x y := by funext j; simp [ratEmb, ratCoords_add]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem ratEmb_injective : Function.Injective (ratEmb (ι := ι) b) := fun x y h => by
  apply ratCoords_injective b
  funext j
  have := congrFun h j
  simp only [ratEmb] at this
  exact_mod_cast this

theorem ratForm_self_pos (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {x : ι → K ⊗[K] E} (hx : x ≠ 0) : 0 < ratForm H θ x x := by
  have : (0 : ℝ) < (ratForm H θ x x : ℝ) := by
    rw [ratForm, trace_eq_sum_realEmb hreal]
    exact Finset.sum_pos (fun w _ => realEmb_mul_hermTrace_pos hθ (hreal w) hx) Finset.univ_nonempty
  exact_mod_cast this


end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

section Sums

variable {H : Matrix ι ι E}

end Sums

def basisOfCard {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    {n : Type*} [Fintype n] {v : n → M} (hli : LinearIndependent k v)
    (hcard : Fintype.card n = finrank k M) : Basis n k M :=
  Basis.mk hli (by
    have h1 := (linearIndependent_iff_card_eq_finrank_span.1 hli)
    refine (Submodule.eq_top_of_finrank_eq ?_).ge
    rw [← hcard, h1]
    rfl)

theorem basisOfCard_apply {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {n : Type*} [Fintype n] {v : n → M} (hli : LinearIndependent k v)
    (hcard : Fintype.card n = finrank k M) (i : n) : basisOfCard hli hcard i = v i :=
  Basis.mk_apply _ _ _

section Reconstruct

variable {H : Matrix ι ι E}

omit [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι]
  [Fintype κ] in
theorem linearIndependent_ratCoords {E : Type*} [CommRing E] [Algebra K E] {N : ℕ}
    {b : Basis κ K E} {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) :
    LinearIndependent ℚ fun i => ratCoords b (x i) := by
  rw [Fintype.linearIndependent_iff] at *
  intro g hg i
  have := hli (fun i => (g i : ℝ)) (by
    funext j
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    simp only [ratEmb]
    exact_mod_cast this) i
  exact_mod_cast this

end Reconstruct

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

section Arithmetic

variable {K : Type*} [Field K] [NumberField K]

theorem exists_int_trace_eq {t : K} (ht : IsIntegral ℤ t) : ∃ n : ℤ, Algebra.trace ℚ K t = n :=
  ⟨Algebra.trace ℤ (𝓞 K) ⟨t, ht⟩, (Algebra.coe_trace_int (K := K) ⟨t, ht⟩).symm⟩

theorem exists_int_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ t : K, (∀ s, ∃ n : ℤ, Algebra.trace ℚ K (t * integralBasis K s) = n) →
      IsIntegral ℤ ((D : K) * t) := by
  classical
  let B := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_isIntegral (Finset.univ.image fun s => B s)
  refine ⟨D, hD0, fun t ht => ?_⟩
  have hexp : t = ∑ s, (Algebra.trace ℚ K (t * integralBasis K s) : K) * B s := by
    conv_lhs => rw [← B.sum_repr t]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Rat.smul_def]
  rw [hexp, Finset.mul_sum]
  refine IsIntegral.sum _ fun s _ => ?_
  obtain ⟨n, hn⟩ := ht s
  rw [hn, Rat.cast_intCast, mul_left_comm]
  exact (isIntegral_algebraMap (x := n)).mul (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ s)))

end Arithmetic

section Cramer

theorem exists_int_factorial_mul_of_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℤ) (hZ : Z.det ≠ 0) (B : ℕ) (hB : Z.det.natAbs ≤ B) (c : n → ℚ)
    (hc : ∀ j, ∃ m : ℤ, (Z.map (Int.cast : ℤ → ℚ) *ᵥ c) j = m) (i : n) :
    ∃ m : ℤ, (B.factorial : ℚ) * c i = m := by
  choose w hw using hc
  have hZc : Z.map (Int.cast : ℤ → ℚ) *ᵥ c = fun j => (w j : ℚ) := funext hw
  have hadj : (Z.adjugate.map (Int.cast : ℤ → ℚ)) * Z.map (Int.cast : ℤ → ℚ) =
      (Z.det : ℚ) • (1 : Matrix n n ℚ) := by
    have h := congrArg (Int.castRingHom ℚ).mapMatrix (Matrix.adjugate_mul Z)
    simp only [map_mul, RingHom.mapMatrix_apply, Int.coe_castRingHom] at h
    rw [h]
    ext a b
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdetc : (Z.det : ℚ) • c = fun j => ((Z.adjugate *ᵥ w) j : ℚ) := by
    rw [← one_mulVec c, ← smul_mulVec, ← hadj, ← mulVec_mulVec, hZc]
    funext j
    simp [mulVec, dotProduct]
  have hdvd : Z.det ∣ (B.factorial : ℤ) := by
    rw [← Int.natAbs_dvd]
    exact_mod_cast Nat.dvd_factorial (Int.natAbs_pos.2 hZ) hB
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q * (Z.adjugate *ᵥ w) i, ?_⟩
  have := congrFun hdetc i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [show (B.factorial : ℚ) = ((Z.det * q : ℤ) : ℚ) by rw [← hq]; norm_cast]
  rw [Int.cast_mul, Int.cast_mul, mul_comm (Z.det : ℚ) (q : ℚ), mul_assoc, this]

end Cramer

section FiniteSets


end FiniteSets

section ShortBasis

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

omit [Fintype κ] [DecidableEq κ] in
theorem intBasis_smul_mem_adelicLattice {b : Basis κ K E}
    {g : unitaryPoints K E H (FinAdele K)} {x : ι → K ⊗[K] E} (hx : x ∈ adelicLattice b H g)
    (s : IntBasisIdx K) : (integralBasis K s) • x ∈ adelicLattice b H g := by
  have := intSmul_mem_adelicLattice hx (RingOfIntegers.basis K s)
  rwa [integralBasis_apply]



end ShortBasis

section Coordinates

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

omit [DecidableEq ι] [DecidableEq κ] in
theorem card_fin_eq_finrank {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) :
    Fintype.card (Fin N) = finrank ℚ ((ι × κ) × IntBasisIdx K → ℚ) := by
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hN]

omit [DecidableEq ι] in
theorem ratForm_sum_left' {ι' : Type*} (θ : K) (s : Finset ι') (v : ι' → ι → K ⊗[K] E)
    (y : ι → K ⊗[K] E) : ratForm H θ (∑ i ∈ s, v i) y = ∑ i ∈ s, ratForm H θ (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := ratForm_add_left (H := H) θ 0 0 y
    rw [add_zero] at this
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratForm_add_left, ih]

omit [DecidableEq ι] in
theorem ratForm_sum_right' {ι' : Type*} (θ : K) (s : Finset ι') (x : ι → K ⊗[K] E)
    (v : ι' → ι → K ⊗[K] E) : ratForm H θ x (∑ i ∈ s, v i) = ∑ i ∈ s, ratForm H θ x (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := ratForm_add_right (H := H) θ x 0 0
    rw [add_zero] at this
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ratForm_add_right, ih]

def ratBasis {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) :
    Basis (Fin N) ℚ ((ι × κ) × IntBasisIdx K → ℚ) :=
  basisOfCard (linearIndependent_ratCoords hli) (card_fin_eq_finrank hN)

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem ratBasis_apply {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (i : Fin N) :
    ratBasis b hN hli i = ratCoords b (x i) :=
  basisOfCard_apply _ _ _

def basisCoords {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (y : ι → K ⊗[K] E) : Fin N → ℚ :=
  fun i => (ratBasis b hN hli).repr (ratCoords b y) i

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem eq_sum_basisCoords {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i))
    (y : ι → K ⊗[K] E) : y = ∑ i, (basisCoords b hN hli y i : K) • x i := by
  apply ratCoords_injective b
  rw [ratCoords_sum]
  simp only [ratCoords_smul, ← ratBasis_apply b hN hli, basisCoords]
  exact ((ratBasis b hN hli).sum_repr _).symm

omit [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [DecidableEq κ] in
theorem basisCoords_sum {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K))
    {x : Fin N → ι → K ⊗[K] E} (hli : LinearIndependent ℝ fun i => ratEmb b (x i))
    (c : Fin N → ℚ) : basisCoords b hN hli (∑ i, (c i : K) • x i) = c := by
  funext i
  simp only [basisCoords, ratCoords_sum, ratCoords_smul, ← ratBasis_apply b hN hli]
  have : ∑ i, c i • ratBasis b hN hli i = (ratBasis b hN hli).equivFun.symm c :=
    (Basis.equivFun_symm_apply _ _).symm
  rw [this]
  exact congrFun ((ratBasis b hN hli).equivFun.apply_symm_apply c) i

omit [DecidableEq κ] in

theorem exists_int_factorial_mul_basisCoords (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {c₀ : ℤ} (hc₀ : c₀ ≠ 0) {L : AddSubgroup (ι → K ⊗[K] E)}
    (hQint : ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, (c₀ : ℚ) * ratForm H θ x y = n)
    {N : ℕ} (hN : N = Fintype.card ((ι × κ) × IntBasisIdx K)) {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) (hxL : ∀ i, x i ∈ L) {M : ℚ}
    (hM : ∀ i j, |ratForm H θ (x i) (x j)| ≤ M) (y : ι → K ⊗[K] E) (hy : y ∈ L) (i : Fin N) :
    ∃ n : ℤ, ((N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N).factorial : ℚ) * basisCoords b hN hli y i = n := by
  classical
  choose Z hZ using fun (j i : Fin N) => hQint (x i) (hxL i) (x j) (hxL j)
  set Zm : Matrix (Fin N) (Fin N) ℤ := Matrix.of Z
  set c := basisCoords b hN hli y
  have hyc : y = ∑ i, (c i : K) • x i := eq_sum_basisCoords b hN hli y

  have hZc : ∀ j, ∃ m : ℤ, (Zm.map (Int.cast : ℤ → ℚ) *ᵥ c) j = m := by
    intro j
    obtain ⟨n, hn⟩ := hQint y hy (x j) (hxL j)
    refine ⟨n, ?_⟩
    rw [← hn]
    conv_rhs => rw [hyc, ratForm_sum_left', Finset.mul_sum]
    simp only [mulVec, dotProduct, Matrix.map_apply, Zm, Matrix.of_apply, ← hZ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ratForm_ratSmul_left]
    ring

  have hZ0 : Zm.det ≠ 0 := by
    intro h0
    have h0' : (Zm.map (Int.cast : ℤ → ℚ)).det = 0 := by
      have := RingHom.map_det (Int.castRingHom ℚ) Zm
      rw [h0, map_zero] at this
      simpa [RingHom.mapMatrix_apply] using this.symm
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    set u := ∑ i, (v i : K) • x i
    have hu : ∀ j, ratForm H θ u (x j) = 0 := by
      intro j
      have h := congrFun hv j
      simp only [mulVec, dotProduct, Matrix.map_apply, Zm, Matrix.of_apply, ← hZ,
        Pi.zero_apply] at h
      have : (c₀ : ℚ) * ratForm H θ u (x j) = 0 := by
        rw [ratForm_sum_left', Finset.mul_sum, ← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ratForm_ratSmul_left]
        ring
      exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hc₀)
    have huu : ratForm H θ u u = 0 := by
      conv_lhs => arg 4; rw [show u = ∑ i, (v i : K) • x i from rfl]
      rw [ratForm_sum_right']
      exact Finset.sum_eq_zero fun j _ => by rw [ratForm_ratSmul_right, hu, mul_zero]
    have hu0 : u = 0 := by
      by_contra hne
      have := ratForm_self_pos b hreal hθ hne
      linarith
    apply hv0
    have hc := basisCoords_sum b hN hli v
    rw [show ∑ i, ((v i : ℚ) : K) • x i = u from rfl, hu0] at hc
    rw [← hc]
    funext i
    simp [basisCoords, ratCoords_zero]

  have hZb : Zm.det.natAbs ≤ N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N := by
    have hentry : ∀ j i, |Zm j i| ≤ (⌈|(c₀ : ℚ)| * M⌉₊ : ℤ) := by
      intro j i
      have h1 : ((|Zm j i| : ℤ) : ℚ) = |(c₀ : ℚ)| * |ratForm H θ (x i) (x j)| := by
        simp only [Zm, Matrix.of_apply, Int.cast_abs, ← hZ, abs_mul]
      have h2 : |(c₀ : ℚ)| * |ratForm H θ (x i) (x j)| ≤ |(c₀ : ℚ)| * M :=
        mul_le_mul_of_nonneg_left (hM i j) (abs_nonneg _)
      have h3 : |(c₀ : ℚ)| * M ≤ (⌈|(c₀ : ℚ)| * M⌉₊ : ℚ) := Nat.le_ceil _
      have : ((|Zm j i| : ℤ) : ℚ) ≤ ((⌈|(c₀ : ℚ)| * M⌉₊ : ℤ) : ℚ) := by
        rw [h1]; push_cast; linarith
      exact_mod_cast this
    have hdet := Matrix.det_le (abv := AbsoluteValue.abs) (A := Zm) hentry
    rw [Fintype.card_fin] at hdet
    have : (Zm.det.natAbs : ℤ) ≤ ((N.factorial * ⌈|(c₀ : ℚ)| * M⌉₊ ^ N : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      simpa [nsmul_eq_mul] using hdet
    exact_mod_cast this
  exact exists_int_factorial_mul_of_mulVec Zm hZ0 _ hZb c hZc i

end Coordinates

section EBound

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι E}
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

omit [NumberField K] in

theorem conjBase_mul_self_algebraMap_mul (ω : K) (e : E) :
    conjBase K E K (algebraMap K (K ⊗[K] E) ω * (1 ⊗ₜ[K] e)) *
        (algebraMap K (K ⊗[K] E) ω * (1 ⊗ₜ[K] e)) =
      algebraMap K (K ⊗[K] E) (ω ^ 2 * Algebra.norm K e) := by
  rw [map_mul, conjBase_algebraMap, conjBase_tmul, map_mul, map_pow,
    Algebra.TensorProduct.algebraMap_apply' (Algebra.norm K e), ← mul_conj]
  have h2 : (1 : K) ⊗ₜ[K] (e * conj K E e) = ((1 : K) ⊗ₜ[K] e) * (1 ⊗ₜ[K] conj K E e) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h2]
  ring

omit [NumberField K] [DecidableEq ι] in
theorem hermTrace_smul_smul_of {z : K ⊗[K] E} {n : K}
    (hz : conjBase K E K z * z = algebraMap K (K ⊗[K] E) n) (x : ι → K ⊗[K] E) :
    hermTrace K H K (z • x) (z • x) = n * hermTrace K H K x x := by
  rw [hermTrace, hermPair_smul_smul, hz, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl


end EBound

end GroundTheory.Automorphic
end
end
