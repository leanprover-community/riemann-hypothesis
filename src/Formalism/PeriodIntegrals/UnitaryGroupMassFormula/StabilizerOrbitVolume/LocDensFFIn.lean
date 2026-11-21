import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

section
noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm, ← hs.herm]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]

theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  have h0 := hs.smul_right 0 x 0
  simpa using h0

theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]
  ring

theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := by
  exact (hs.herm x x).symm

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have h1 : ∀ i y, h (b i) y = h' (b i) y := by
    intro i y
    have e := b.ext (f₁ := hs.lin (b i)) (f₂ := hs'.lin (b i)) (fun j => hb i j)
    exact LinearMap.congr_fun e y
  have h3 : ∀ x y, h y x = h' y x := by
    intro x y
    have e := b.ext (f₁ := hs.lin y) (f₂ := hs'.lin y) (fun i => by
      simp only [IsSq.lin_apply]
      rw [hs.herm (b i) y, hs'.herm (b i) y, h1])
    exact LinearMap.congr_fun e x
  exact h3 y x

theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key : ∀ c : K, c * h x y + σ (c * h x y) = 0 := by
    intro c
    have e1 : h (x + c • y) (x + c • y) = h x x + h x (c • y) + (h (c • y) x + h (c • y) (c • y)) := by
      rw [hs.add_right, IsSq.add_left hs.toIsSq, IsSq.add_left hs.toIsSq]
      ring
    rw [H, H, H, hs.herm x (c • y), hs.smul_right] at e1
    linear_combination -e1
  have ha : h x y + σ (h x y) = 0 := by simpa using key 1
  by_cases hσ : ∃ c, σ c ≠ c
  · obtain ⟨c, hc⟩ := hσ
    have e2 := key c
    rw [map_mul] at e2
    have hsa : σ (h x y) = -(h x y) := by linear_combination ha
    rw [hsa] at e2
    have e3 : (c - σ c) * h x y = 0 := by linear_combination e2
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact hc (by linear_combination -h0)
    · exact hy h0
  · push_neg at hσ
    rw [hσ] at ha
    have e3 : (2 : K) * h x y = 0 := by linear_combination ha
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact h2 h0
    · exact hy h0

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by
  exact LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : LinearMap.range (hs.lin e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / h e e) • e, ?_⟩
    rw [IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]
  have e1 := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [hsurj, finrank_top, Module.finrank_self] at e1
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero] at e1
  simp only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1
  rw [Finset.sum_eq_single i] at e1
  · exact (mul_eq_zero.1 e1).resolve_right (h2 i)
  · intro j _ hji
    rw [h1 i j (Ne.symm hji), mul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  have hwe : h w e = 0 := by rw [hs.herm e w, hw, map_zero]
  rw [hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right,
    hs.smul_right, hw, hwe]
  ring

end basic

theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hs hm
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hp := perp_isHS hs e he
    have hr := finrank_perp hs.toIsSq e he
    obtain ⟨g, hg1, hg2⟩ := ih (perp hs.toIsSq e) (fun w w' => h w w') hp (by omega)
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (mem_perp hs.toIsSq e _).1 (g _).2
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hs.herm e, (mem_perp hs.toIsSq e _).1 (g _).2, map_zero]
      · simp only [Fin.cons_succ]
        exact hg1 _ _ (fun h' => hij (by rw [h']))
    · intro i
      induction i using Fin.cases
      · simpa using he
      · simpa using hg2 _

end PI.VolStabSW.FFHS
end
end

section
noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem perp_sub_mem {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right, mul_right_comm, inv_mul_cancel₀ he, one_mul, sub_self]

theorem card_decomp {V : Type} [AddCommGroup V] [Module K V] [Finite V] {h : V → V → K}
    (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) (c : K) :
    Nat.card {x : V // h x x = c} =
      ∑ t : K, Nat.card {w : perp hs e // h w w = c - σ t * t * h e e} := by
  classical
  let T : V → K := fun x => (h e e)⁻¹ * h e x
  have hTe : ∀ (t : K) (w : perp hs e), T ((t • e) + (w : V)) = t := by
    intro t w
    simp only [T]
    rw [hs.add_right, hs.smul_right, (mem_perp hs e w).1 w.2, add_zero, ← mul_assoc,
      mul_comm ((h e e)⁻¹) t, mul_assoc, inv_mul_cancel₀ he, mul_one]
  let eqv : {x : V // h x x = c} ≃ Σ t : K, {w : perp hs e // h w w = c - σ t * t * h e e} :=
    { toFun := fun x => ⟨T x.1, ⟨⟨x.1 - T x.1 • e, perp_sub_mem hs e x.1 he⟩, by
        have h1 := decomp_val hs e (x.1 - T x.1 • e)
          ((mem_perp hs e _).1 (perp_sub_mem hs e x.1 he)) (T x.1)
        have hx : T x.1 • e + (x.1 - T x.1 • e) = x.1 := by abel
        rw [hx, x.2] at h1
        show h (x.1 - T x.1 • e) (x.1 - T x.1 • e) = c - σ (T x.1) * T x.1 * h e e
        rw [eq_sub_iff_add_eq, add_comm]
        exact h1.symm⟩⟩
      invFun := fun p => ⟨p.1 • e + (p.2.1 : V), by
        rw [decomp_val hs e p.2.1 ((mem_perp hs e _).1 p.2.1.2) p.1]
        have h2 : h (p.2.1 : V) (p.2.1 : V) = c - σ p.1 * p.1 * h e e := p.2.2
        rw [h2]
        ring⟩
      left_inv := fun x => Subtype.ext (by
        show T x.1 • e + (x.1 - T x.1 • e) = x.1
        abel)
      right_inv := fun p => by
        refine Sigma.subtype_ext (hTe p.1 p.2.1) (Subtype.ext ?_)
        show p.1 • e + (p.2.1 : V) - T (p.1 • e + (p.2.1 : V)) • e = (p.2.1 : V)
        rw [hTe]
        abel }
  rw [Nat.card_congr eqv, Nat.card_sigma]

theorem card_norm (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hh hm c hc
    haveI : Subsingleton V := Module.finrank_zero_iff.1 hm
    have hr : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hcard : Nat.card {x : V // h x x = c} = if c = 0 then 1 else 0 := by
      split_ifs with hc0
      · rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, by rw [hh.toIsSq.zero_left, hc0]⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
      · rw [Nat.card_eq_zero]
        left
        constructor
        intro x
        apply hc0
        rw [← x.2, Subsingleton.elim x.1 0, hh.toIsSq.zero_left]
    rw [hcard]
    split_ifs with hc0
    · push_cast
      field_simp
      ring
    · push_cast
      ring
  | succ m ih =>
    intro V _ _ _ h hh hm c hc
    haveI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    haveI : Finite V := Module.finite_of_finite K
    obtain ⟨x0, hx0⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hh x0 hx0
    have hdec := card_decomp hh.toIsSq e he c
    have haσ : σ (h e e) = h e e := hh.toIsSq.self_fixed e
    have hperp := perp_isHS hh e he
    have hfr : finrank K (perp hh.toIsSq e) = m := by
      have := finrank_perp hh.toIsSq e he
      omega
    have hterm : ∀ t : K, (Nat.card {w : perp hh.toIsSq e // h w w = c - σ t * t * h e e} : ℝ) =
        (q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1) := by
      intro t
      have hfix : σ (c - σ t * t * h e e) = c - σ t * t * h e e := by
        rw [map_sub, map_mul, map_mul, hσ, hc, haσ]
        ring
      exact ih (perp hh.toIsSq e) (fun w w' => h w w') hperp hfr _ hfix
    have hP : ∀ t : K, (c - σ t * t * h e e = 0) ↔ t * σ t = c / h e e := by
      intro t
      rw [sub_eq_zero, eq_div_iff he]
      exact ⟨fun h' => by rw [h']; ring, fun h' => by rw [← h']; ring⟩
    have hcnt : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q:ℝ) + 1 := by
      have hfixd : σ (c / h e e) = c / h e e := by rw [map_div₀, hc, haσ]
      have h3 := hN (c / h e e) hfixd
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
      have h4 : (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)) =
          Finset.univ.filter (fun t => t * σ t = c / h e e) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hP t
      rw [h4, h3]
      have h5 : c / h e e = 0 ↔ c = 0 := div_eq_zero_iff.trans (or_iff_left he)
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp [hc0, h5]
    have hsum : ∑ t : K, ((q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1)) =
        (q:ℝ) * (q:ℝ) * ((q:ℝ) ^ (2 * (m:ℤ) - 1) - (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1)) +
          (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) * (q:ℝ) *
            (Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card := by
      have e1 : ∀ t : K, ((q:ℝ) ^ (2 * (m:ℤ) - 1) + (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q:ℝ) else 0) - 1)) =
          ((q:ℝ) ^ (2 * (m:ℤ) - 1) - (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1)) +
            (-1) ^ m * (q:ℝ) ^ ((m:ℤ) - 1) * (if c - σ t * t * h e e = 0 then (q:ℝ) else 0) :=
        fun t => by ring
      rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, hK, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [hdec, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hterm t), hsum, hcnt]
    have hr : (q:ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have e2 : (q:ℝ) ^ (2 * ((m + 1 : ℕ) : ℤ) - 1) = (q:ℝ) * (q:ℝ) * (q:ℝ) ^ (2 * (m:ℤ) - 1) := by
      rw [show (2 * ((m + 1 : ℕ) : ℤ) - 1) = 1 + 1 + (2 * (m:ℤ) - 1) by push_cast; ring,
        zpow_add₀ hr, zpow_add₀ hr, zpow_one]
    have e3 : (q:ℝ) ^ (((m + 1 : ℕ) : ℤ) - 1) = (q:ℝ) * (q:ℝ) ^ ((m:ℤ) - 1) := by
      rw [show (((m + 1 : ℕ) : ℤ) - 1) = 1 + ((m:ℤ) - 1) by push_cast; ring, zpow_add₀ hr, zpow_one]
    rw [e2, e3, pow_succ]
    split_ifs <;> ring

theorem card_diag (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : K) ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  intro a
  induction a with
  | zero =>
    intro m _ V _ _ _ h hh hm d hd hd0
    rw [Fin.prod_univ_zero]
    have h1 : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.2
        ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun Y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    rw [h1]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hh hm d hd hd0
    classical
    haveI : Finite V := Module.finite_of_finite K
    haveI := Fintype.ofFinite V
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    let eqv : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y0 : {x : V // h x x = d 0}, {Y' : Fin a → perp hh.toIsSq y0.1 //
          ∀ i j, h (Y' i : V) (Y' j : V) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩, ⟨fun i => ⟨Y.1 i.succ, by
            rw [mem_perp]
            have h3 := Y.2 0 i.succ
            rwa [if_neg (Fin.succ_ne_zero i).symm] at h3⟩,
          fun i j => by
            have h3 := Y.2 i.succ j.succ
            simpa [Fin.succ_inj] using h3⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), by
          intro i j
          refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
          · simpa using p.1.2
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero j).symm]
            exact (mem_perp _ _ _).1 (p.2.1 j).2
          · simp only [Fin.cons_zero, Fin.cons_succ]
            rw [if_neg (Fin.succ_ne_zero i), hh.toIsSq.herm p.1.1 (p.2.1 i),
              (mem_perp _ _ _).1 (p.2.1 i).2, map_zero]
          · simp only [Fin.cons_succ, Fin.succ_inj]
            exact p.2.2 i j⟩
        left_inv := fun Y => Subtype.ext (Fin.cons_self_tail Y.1)
        right_inv := fun p => rfl }
    rw [Nat.card_congr eqv, Nat.card_sigma, Nat.cast_sum]
    have hfib : ∀ y0 : {x : V // h x x = d 0}, (Nat.card {Y' : Fin a → perp hh.toIsSq y0.1 //
          ∀ i j, h (Y' i : V) (Y' j : V) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q:ℝ) ^ (m' - j - 1)) := by
      intro y0
      have hy0 : h y0.1 y0.1 ≠ 0 := by rw [y0.2]; exact hd0 0
      have hfr : finrank K (perp hh.toIsSq y0.1) = m' := by
        have := finrank_perp hh.toIsSq y0.1 hy0
        omega
      exact ih m' (by omega) (perp hh.toIsSq y0.1) (fun w w' => h w w') (perp_isHS hh y0.1 hy0) hfr
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    rw [Finset.sum_congr rfl (fun y0 _ => hfib y0), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN0 := card_norm q hq0 hK hσ h2 hN (m' + 1) V h hh hm (d 0) (hd 0)
    rw [← Nat.card_eq_fintype_card, hN0, if_neg (hd0 0), Fin.prod_univ_succ]
    have z1 : (q:ℝ) ^ (2 * ((m' + 1 : ℕ) : ℤ) - 1) = (q:ℝ) ^ (2 * (m' + 1 - ((0 : Fin (a + 1)) : ℕ)) - 1) := by
      rw [← zpow_natCast]
      congr 1
      simp only [Fin.val_zero]
      omega
    have z2 : (q:ℝ) ^ (((m' + 1 : ℕ) : ℤ) - 1) = (q:ℝ) ^ (m' + 1 - ((0 : Fin (a + 1)) : ℕ) - 1) := by
      rw [← zpow_natCast]
      congr 1
      simp only [Fin.val_zero]
      omega
    rw [z1, z2]
    have hP : ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' + 1 - (j.succ : ℕ)) - 1) -
        (-1) ^ (m' + 1 - (j.succ : ℕ)) * (q:ℝ) ^ (m' + 1 - (j.succ : ℕ) - 1)) =
        ∏ j : Fin a, ((q:ℝ) ^ (2 * (m' - j) - 1) - (-1) ^ (m' - j) * (q:ℝ) ^ (m' - j - 1)) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Fin.val_succ, Nat.add_sub_add_right]
    rw [hP]
    simp only [Fin.val_zero, Nat.sub_zero]
    ring

end PI.VolStabSW.FFHS
end
end

section
noncomputable section

namespace PI.VolStabSW.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  have hs : ∀ i' : Fin n, σ ((Pi.single i 1 : Fin n → K) i') = (Pi.single i 1 : Fin n → K) i' := by
    intro i'
    by_cases h : i' = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  simp only [PI.VolStabSW.ffH, hs]
  simp [Pi.single_apply]

end matrix

theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by
  refine Nat.card_congr
    { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩
      invFun := fun Y => ⟨b.constr K Y.1, fun x y => ?_⟩
      left_inv := fun φ => ?_
      right_inv := fun Y => ?_ }
  · have hs1 : IsSq σ (fun x y => hV (b.constr K Y.1 x) (b.constr K Y.1 y)) :=
      { add_right := fun x y z => by
          simp only [map_add]
          exact hsV.add_right _ _ _
        smul_right := fun c x y => by
          simp only [map_smul]
          exact hsV.smul_right _ _ _
        herm := fun x y => hsV.herm _ _ }
    exact hs1.ext_basis hsU b (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y
  · apply Subtype.ext
    exact b.ext fun i => by simp [Basis.constr_basis]
  · apply Subtype.ext
    funext i
    simp [Basis.constr_basis]

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

private theorem card_le_natDegree_of_eval_eq_zero {L : Type} [Field L] (P : L[X]) (hP : P ≠ 0)
    (Z : Finset L) (hZ : ∀ z ∈ Z, P.eval z = 0) : Z.card ≤ P.natDegree := by
  have hsub : Z.val ⊆ P.roots := fun z hz =>
    (Polynomial.mem_roots hP).mpr (hZ z (Finset.mem_val.mp hz))
  exact (Multiset.card_le_card ((Multiset.le_iff_subset Z.nodup).mpr hsub)).trans
    (Polynomial.card_roots' P)

private theorem card_le_of_pow_eq_mul_add {L : Type} [Field L] (n : ℕ) (hn : 1 < n) (b c : L)
    (Z : Finset L) (hZ : ∀ z ∈ Z, z ^ n = b * z + c) : Z.card ≤ n := by
  have hlt : (C b * X + C c : L[X]).natDegree < (X ^ n : L[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt Polynomial.natDegree_linear_le hn
  have hdeg : (X ^ n - (C b * X + C c) : L[X]).natDegree = n := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hP0 : (X ^ n - (C b * X + C c) : L[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have := card_le_natDegree_of_eval_eq_zero _ hP0 Z fun z hz => by simp [hZ z hz]
  rwa [hdeg] at this

private theorem exists_algebraMap_eq_of_frobenius_fixed (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  by_contra hne
  push_neg at hne
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hdS : d ∉ Finset.univ.image (algebraMap k K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hc := card_le_of_pow_eq_mul_add (Fintype.card k) hq 1 0
    (Finset.cons d (Finset.univ.image (algebraMap k K)) hdS) (by
      intro z hz
      rw [Finset.mem_cons] at hz
      rcases hz with h | hz
      · rw [h, hd, one_mul, add_zero]
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
        rw [← map_pow, FiniteField.pow_card, one_mul, add_zero])
  rw [Finset.card_cons, Finset.card_image_of_injective _ (algebraMap k K).injective,
    Finset.card_univ] at hc
  omega

theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  intro x
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  by_cases hx : ∃ a : k, algebraMap k K a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [AlgEquiv.commutes, ← map_pow, FiniteField.pow_card]
  push_neg at hx
  have hq : x ^ Fintype.card k ≠ x := fun h => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_frobenius_fixed x h
    exact hx a ha
  have hσx : σ x ≠ x := by
    intro hfix
    apply hne
    have hli : LinearIndependent k ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        exact ⟨by simpa using hst, rfl⟩
      · exfalso
        have htK : algebraMap k K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        apply hx (-s * t⁻¹)
        rw [map_mul, map_neg, map_inv₀, eq_comm, eq_mul_inv_iff_mul_eq₀ htK]
        linear_combination hst
    have hlin : σ.toLinearMap = LinearMap.id :=
      (basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])).ext fun i => by
        fin_cases i <;> simp [coe_basisOfLinearIndependentOfCardEqFinrank, hfix]
    ext y
    simpa using LinearMap.congr_fun hlin y
  have hint_r : IsIntegral k x := IsIntegral.of_finite k x
  have hP0 : (minpoly k x).map (algebraMap k K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint_r)
  have hroot : ∀ y, Polynomial.aeval y (minpoly k x) = 0 →
      ((minpoly k x).map (algebraMap k K)).eval y = 0 := fun y hy => by
    rw [Polynomial.eval_map_algebraMap]
    exact hy
  have r1 := hroot x (minpoly.aeval k x)
  have r2 := hroot (σ x) (by
    rw [show σ x = (σ : K →ₐ[k] K) x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero])
  have r3 := hroot (x ^ Fintype.card k) (by
    rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval,
      zero_pow Fintype.card_ne_zero])
  by_contra hne3
  have hcard : ({x, σ x, x ^ Fintype.card k} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, σ x, x ^ Fintype.card k, hσx.symm, hq.symm, hne3, rfl⟩
  have hle := card_le_natDegree_of_eval_eq_zero _ hP0 {x, σ x, x ^ Fintype.card k} (by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h <;> rw [h] <;> assumption)
  rw [hcard, Polynomial.natDegree_map] at hle
  have hdeg : (minpoly k x).natDegree ≤ finrank k K := minpoly.natDegree_le x
  omega

theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hKcard' : Fintype.card K = Fintype.card k ^ finrank k K := Module.card_eq_pow_finrank
  have hKcard : Fintype.card K = Fintype.card k ^ 2 := by rw [hKcard', h2]
  have hσσ : ∀ t, σ (σ t) = t := by
    intro t
    rw [hfrob (σ t), hfrob t, ← pow_mul, ← sq, ← hKcard, FiniteField.pow_card]
  let c : K → ℕ := fun y => (Finset.univ.filter fun t : K => t * σ t = y).card
  let F : Finset K := Finset.univ.filter fun y : K => y ^ Fintype.card k = y
  have hsum : Fintype.card K = ∑ y ∈ F, c y := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := fun t => t * σ t) fun t _ => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, map_mul, hσσ, mul_comm]
  have hF : F.card ≤ Fintype.card k :=
    card_le_of_pow_eq_mul_add _ hq1 1 0 F fun z hz => by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [hz, one_mul, add_zero]
  have hfib : ∀ y, c y ≤ Fintype.card k + 1 := fun y =>
    card_le_of_pow_eq_mul_add _ (by omega) 0 y (Finset.univ.filter fun t : K => t * σ t = y)
      fun t ht => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [pow_succ', ← hfrob, ht, zero_mul, zero_add]
  have hc0 : c 0 = 1 := by
    show (Finset.univ.filter fun t : K => t * σ t = 0).card = 1
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext t
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  split_ifs with hd0
  · subst hd0
    exact hc0
  · have hdF : d ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, hd]
    have h0F : (0 : K) ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact zero_pow (by omega)
    refine le_antisymm (hfib d) ?_
    by_contra hlt
    push_neg at hlt
    have key : ∑ y ∈ F.erase 0, c y < ∑ _y ∈ F.erase 0, (Fintype.card k + 1) :=
      Finset.sum_lt_sum (fun y _ => hfib y) ⟨d, Finset.mem_erase.mpr ⟨hd0, hdF⟩, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0F] at key
    have hs := Finset.add_sum_erase F c h0F
    rw [hc0] at hs
    have hn : 1 ≤ F.card := Finset.card_pos.mpr ⟨0, h0F⟩
    have h3 : (F.card - 1) * (Fintype.card k + 1) ≤
        (Fintype.card k - 1) * (Fintype.card k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (Fintype.card k - 1) * (Fintype.card k + 1) + 1 = Fintype.card k ^ 2 := by
      obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      ring
    omega

end field

theorem fFInert_holds : FFInert := by
  unfold PI.VolStabSW.FFInert
  intro k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdet T hT hTdet
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K := Module.finite_of_finite k
  haveI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ h2 hne
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at this
  have hK' : Fintype.card K = Fintype.card k ^ Module.finrank k K := Module.card_eq_pow_finrank
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [hK', h2, Nat.card_eq_fintype_card]
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob h2 d hd
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hsV := ffH_isHS hσ' J hJ hdet
  have hsU := ffH_isHS hσ' T hT hTdet
  obtain ⟨f, horth, hnz⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabSW.ffH (σ : K →+* K) T) hsU (Module.finrank_fin_fun K)
  have hli := linIndep_orth hsU.toIsSq f horth hnz
  have hsp : Submodule.span K (Set.range f) = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun])
  let bf := Module.Basis.mk hli hsp.ge
  have hbf : ∀ i, bf i = f i := fun i => Module.Basis.mk_apply hli hsp.ge i
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabSW.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        PI.VolStabSW.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      exact congrFun (congrFun h i) j
    · intro h
      ext i j
      exact h i j
  have e2 := card_isom hsU.toIsSq
    hsV.toIsSq (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq
    hsV.toIsSq bf
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        PI.VolStabSW.ffH (σ : K →+* K) T (bf i) (bf j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hg : ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) T (bf i) (bf j) =
        if i = j then PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      simp only [hbf]
      split_ifs with hij
      · rw [hij]
      · exact horth i j hij
    refine Nat.card_congr (Equiv.subtypeEquivRight fun Y => ?_)
    simp only [hg]
  rw [e1, ← e2, e3, e4]
  exact card_diag (Nat.card k) hq0 hK hσ' h2K hN a M haM
    (Fin M → K) (PI.VolStabSW.ffH (σ : K →+* K) J) hsV (Module.finrank_fin_fun K)
    (fun i => PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hnz

end PI.VolStabSW.FFHS
end
end
