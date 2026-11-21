import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem swap_lt_iff {n : ℕ} (i j x y : Fin n) (h : (j : ℕ) = i + 1)
    (h1 : ¬ (x = i ∧ y = j)) (h2 : ¬ (x = j ∧ y = i)) :
    Equiv.swap i j x < Equiv.swap i j y ↔ x < y := by
  have key : ∀ z : Fin n, (z = i ∧ Equiv.swap i j z = j) ∨ (z = j ∧ Equiv.swap i j z = i) ∨
      (z ≠ i ∧ z ≠ j ∧ Equiv.swap i j z = z) := by
    intro z
    by_cases hi : z = i
    · left; subst hi; simp
    · by_cases hj : z = j
      · right; left; subst hj; simp
      · right; right; exact ⟨hi, hj, Equiv.swap_apply_of_ne_of_ne hi hj⟩
  rcases key x with ⟨hx, ex⟩ | ⟨hx, ex⟩ | ⟨hx1, hx2, ex⟩ <;>
  rcases key y with ⟨hy, ey⟩ | ⟨hy, ey⟩ | ⟨hy1, hy2, ey⟩ <;>
  rw [ex, ey] <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, ne_eq] at * <;>
  constructor <;> intro <;> omega

private theorem len_up {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) : invLen (Equiv.swap i j * w) = invLen w + 1 := by
  have hij : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  show (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1)).card =
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1)).card + 1
  rw [show Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ (Equiv.swap i j * w) p.2 < (Equiv.swap i j * w) p.1) =
    insert (w⁻¹ i, w⁻¹ j) (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1))
    from ?_]
  · apply Finset.card_insert_of_notMem
    simp [hij.le]
  · ext ⟨x, y⟩
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Prod.mk.injEq, Equiv.Perm.mul_apply]
    by_cases hxy : x = w⁻¹ i ∧ y = w⁻¹ j
    · obtain ⟨rfl, rfl⟩ := hxy
      simp [hij]
      exact hw
    · rw [or_iff_right hxy]
      apply and_congr_right
      intro hlt
      apply swap_lt_iff i j _ _ h
      · rintro ⟨h1, h2⟩
        have e1 : y = w⁻¹ i := by rw [← h1]; simp
        have e2 : x = w⁻¹ j := by rw [← h2]; simp
        subst e1 e2
        exact absurd hlt (not_lt.mpr hw.le)
      · rintro ⟨h1, h2⟩
        exact hxy ⟨by rw [← h2]; simp, by rw [← h1]; simp⟩

private theorem len_down {n : ℕ} (w : Equiv.Perm (Fin n)) (i j : Fin n) (h : (j : ℕ) = i + 1)
    (hw : w⁻¹ j < w⁻¹ i) : invLen (Equiv.swap i j * w) + 1 = invLen w := by
  have key := len_up (Equiv.swap i j * w) i j h
    (by simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hw)
  rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at key
  exact key.symm

private theorem exists_desc {n : ℕ} (w : Equiv.Perm (Fin n)) (hw : w ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i := by
  by_contra hne
  push_neg at hne
  apply hw
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hmono : StrictMono (⇑w⁻¹) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      refine lt_of_le_of_ne (hne _ _ (by simp)) (fun e => ?_)
      exact absurd (w⁻¹.injective e) Fin.castSucc_lt_succ.ne
    have hid : (⇑w⁻¹) = id := (hmono.range_inj strictMono_id).1 (by simp)
    rw [← inv_eq_one]
    ext x
    simp [congrFun hid x]

theorem UpperTheory.V.AlgebraTools.lenStep :
    ∀ (n : ℕ) (w : Equiv.Perm (Fin n)), (∀ (i j : Fin n), (j : ℕ) = i + 1 → (w⁻¹ i < w⁻¹ j → invLen (Equiv.swap i j * w) = invLen w + 1) ∧ (w⁻¹ j < w⁻¹ i → invLen (Equiv.swap i j * w) + 1 = invLen w)) ∧ (invLen w = 0 → w = 1) ∧ (w ≠ 1 → ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ w⁻¹ j < w⁻¹ i) := by
  intro n w
  refine ⟨fun i j h => ⟨len_up w i j h, len_down w i j h⟩, fun h0 => ?_, exists_desc w⟩
  by_contra hw
  obtain ⟨i, j, h, hlt⟩ := exists_desc w hw
  have := len_down w i j h hlt
  omega
end

section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools.PermCard

private theorem conj_apply {R : Type} [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  rw [← map_inv, Units.val_mul, Units.val_mul]
  simp only [mul_apply, pm_apply]
  rw [Fintype.sum_eq_single (w b), Fintype.sum_eq_single (w a)]
  · simp
  · intro x hx
    rw [if_neg, zero_mul]
    rintro rfl
    exact hx (by simp)
  · intro x hx
    rw [if_neg hx, mul_zero]

private theorem map_pm {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (w : Equiv.Perm (Fin n)) :
    GeneralLinearGroup.map (n := Fin n) f (pm R n w) = pm S n w := by
  ext i j
  show f ((pm R n w : Matrix (Fin n) (Fin n) R) i j) = _
  rw [pm_apply, pm_apply]
  split_ifs <;> simp

private theorem ncard_orbit {G ι : Type} [Group G] (I : Subgroup G) (s w : G) (x : ι → G) (hx : ∀ c, x c ∈ I)
    (h1 : ∀ g ∈ I, ∃ c, ∃ b ∈ I, g * s = x c * s * b)
    (h2 : ∀ g ∈ I, ∃ c, ∃ b ∈ I, s * g = b * (s * x c))
    (h3 : ∀ c, w⁻¹ * x c * w ∈ I)
    (h4 : ∀ c c', ∀ g ∈ I, ∀ g' ∈ I, w⁻¹ * (g'⁻¹ * (s⁻¹ * ((x c')⁻¹ * x c) * s) * g) * w ∈ I → c = c') :
    (MulAction.orbit I ((s * w : G) : G ⧸ I)).ncard = Nat.card ι * (MulAction.orbit I (w : G ⧸ I)).ncard := by
  have hm : ∀ (c : ι) (q : MulAction.orbit I (w : G ⧸ I)),
      (x c * s) • (q : G ⧸ I) ∈ MulAction.orbit I ((s * w : G) : G ⧸ I) := by
    rintro c ⟨_, g, rfl⟩
    obtain ⟨a, b, hb, e⟩ := h2 g g.2
    refine ⟨⟨x c * b, mul_mem (hx c) hb⟩, ?_⟩
    show ((x c * b * (s * w) : G) : G ⧸ I) = ((x c * s * (g * w) : G) : G ⧸ I)
    rw [QuotientGroup.eq]
    have : x c * s * (g * w) = x c * (s * g) * w := by group
    rw [this, e]
    convert h3 a using 1
    group
  let f : ι × MulAction.orbit I (w : G ⧸ I) → MulAction.orbit I ((s * w : G) : G ⧸ I) :=
    fun p => ⟨_, hm p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c, _, g, rfl⟩ ⟨c', _, g', rfl⟩ e
      have e1 : (x c * s) • ((g : G) • (w : G ⧸ I)) = (x c' * s) • ((g' : G) • (w : G ⧸ I)) :=
        congrArg Subtype.val e
      have e2 : ((x c' * s * (g' * w) : G) : G ⧸ I) = ((x c * s * (g * w) : G) : G ⧸ I) := e1.symm
      rw [QuotientGroup.eq] at e2
      have hc : c = c' := h4 c c' g g.2 g' g'.2 (by convert e2 using 1; group)
      subst hc
      exact Prod.ext rfl (Subtype.ext (smul_left_cancel _ e1))
    · rintro ⟨_, g, rfl⟩
      obtain ⟨c, b, hb, e⟩ := h1 g g.2
      refine ⟨(c, ⟨_, ⟨b, hb⟩, rfl⟩), Subtype.ext ?_⟩
      show ((x c * s * (b * w) : G) : G ⧸ I) = ((g * (s * w) : G) : G ⧸ I)
      rw [← mul_assoc, ← e, mul_assoc]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_prod, Nat.card_eq_of_bijective f hf]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem step (C : Subgroup 𝓀[k]ˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1)
    (hw : w⁻¹ i < w⁻¹ j) :
    (MulAction.orbit (iwC k n C) ((pm k n (Equiv.swap i j * w) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard =
      resCard k * (MulAction.orbit (iwC k n C) ((pm k n w : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard := by
  choose r hr using IsLocalRing.residue_surjective (R := 𝒪[k])
  obtain ⟨x, hx, hxu, ho, h2⟩ := simpleOrbit k n C i j hij r hr
  have hU : unipO k n ≤ iwC k n C := le_sup_right.trans le_sup_left
  have hlt : i < j := by rw [Fin.lt_def]; omega
  obtain ⟨hmem, -, -, hun⟩ := memIwC k n C
  have hdiag : ∀ g ∈ iwC k n C, ∀ a, valuation k ((g : Matrix (Fin n) (Fin n) k) a a) = 1 := by
    intro g hg a
    obtain ⟨c, ⟨d, -, rfl⟩, e⟩ := ((hmem g).1 hg).2 a
    rw [← e]
    exact (hun _).1 ⟨d, trivial, rfl⟩
  have hlow : ∀ g ∈ iwC k n C, ∀ a b, b < a → valuation k ((g : Matrix (Fin n) (Fin n) k) a b) < 1 :=
    fun g hg => (mem_iwahori.1 ((hmem g).1 hg).1).2
  rw [map_mul]
  refine ncard_orbit (iwC k n C) _ _ x (fun c => hU (hxu c)) ?_ h2 ?_ ?_
  · intro g hg
    obtain ⟨c, hc, -⟩ := (ho ((g * pm k n (Equiv.swap i j) : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).1
      ⟨⟨g, hg⟩, rfl⟩
    exact ⟨c, _, QuotientGroup.eq.1 hc, by group⟩
  · intro c
    have hK : pm k n w ∈ KO k (Fin n) := ⟨pm 𝒪[k] n w, map_pm _ w⟩
    have hK' : (pm k n w)⁻¹ * x c * pm k n w ∈ KO k (Fin n) := mul_mem (mul_mem (inv_mem hK) (hxu c).2) hK
    refine hU ⟨(mem_unipB k).2 ⟨fun a b hab => ?_, fun a => ?_⟩, hK'⟩
    · rw [conj_apply, hx, Matrix.add_apply, one_apply_ne (w.injective.ne hab.ne'), single_apply, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at hw
      exact lt_asymm hw hab
    · rw [conj_apply, hx, Matrix.add_apply, one_apply_eq, single_apply, if_neg, add_zero]
      rintro ⟨h, h'⟩
      exact hlt.ne (h.trans h'.symm)
  · intro c c' g hg g' hg' h
    set d : k := algebraMap 𝒪[k] k (r c) - algebraMap 𝒪[k] k (r c') with hd
    have hz : (((x c')⁻¹ * x c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 + single i j d := by
      rw [Units.val_mul, Units.inv_mul_eq_iff_eq_mul, hx, hx, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
        single_mul_single_of_ne _ _ _ _ hlt.ne', add_zero, add_assoc, ← single_add, hd, sub_add_cancel]
    have hy : (((pm k n (Equiv.swap i j))⁻¹ * ((x c')⁻¹ * x c) * pm k n (Equiv.swap i j) : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 1 + single j i d := by
      ext a b
      rw [conj_apply, hz]
      simp only [Matrix.add_apply, one_apply, single_apply, Equiv.apply_eq_iff_eq]
      congr 2
      rw [← Equiv.symm_apply_eq, ← Equiv.symm_apply_eq, Equiv.symm_swap, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
    have h5 := hlow _ h _ _ hw
    rw [conj_apply, Units.val_mul, Units.val_mul, hy, mul_add, add_mul, mul_one, Matrix.add_apply] at h5
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h5
    have h6 := hlow _ (mul_mem (inv_mem hg') hg) j i hlt
    rw [Units.val_mul] at h6
    have h7 : (((g'⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * single j i d * (g : Matrix (Fin n) (Fin n) k)) j i =
        ((g'⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) j j * d * (g : Matrix (Fin n) (Fin n) k) i i := by
      rw [mul_apply, Fintype.sum_eq_single i, mul_single_apply_same]
      intro a ha
      rw [mul_single_apply_of_ne _ _ _ _ _ ha, zero_mul]
    have h8 := Valuation.map_sub_lt _ h5 h6
    rw [add_sub_cancel_left, h7, map_mul, map_mul, hdiag _ (inv_mem hg'), hdiag _ hg, one_mul, mul_one, hd,
      ← map_sub] at h8
    have h9 : IsLocalRing.residue 𝒪[k] (r c - r c') = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact h8.ne
    rwa [map_sub, hr, hr, sub_eq_zero] at h9

end UpperTheory.V.AlgebraTools.PermCard

open UpperTheory.V.AlgebraTools.PermCard in
theorem UpperTheory.V.AlgebraTools.permCard :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (w : Equiv.Perm (Fin n)), (MulAction.orbit (iwC k n C) ((pm k n w : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C)).ncard = resCard k ^ invLen w := by
  intro k _ _ _ _ n C w
  generalize hm : invLen w = m
  induction m generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 hm, map_one, pow_zero, Set.ncard_eq_one]
    refine ⟨_, Set.eq_singleton_iff_unique_mem.2 ⟨MulAction.mem_orbit_self _, ?_⟩⟩
    rintro _ ⟨g, rfl⟩
    show (((g : GL (Fin n) k) * 1 : GL (Fin n) k) : GL (Fin n) k ⧸ iwC k n C) = _
    rw [QuotientGroup.eq]
    simpa using g.2
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        rw [invLen, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        exact fun p _ h => lt_asymm h.1 h.2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hl := ((lenStep n w).1 i j hij).2 hlt
    have hs := step C (Equiv.swap i j * w) i j hij (by simpa using hlt)
    rw [Equiv.swap_mul_self_mul] at hs
    rw [hs, ih _ (by omega), pow_succ']
end

section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem pm_conj_apply (R : Type) [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R)
    (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  have hinv : (pm R n w)⁻¹ = pm R n w⁻¹ := (map_inv _ _).symm
  rw [hinv, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp [-map_inv, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq, Equiv.eq_symm_apply]

private theorem pm_mem_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  simp [pm_apply]

private theorem invLen_one (n : ℕ) : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold invLen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  exact lt_asymm h1 h2

theorem UpperTheory.V.AlgebraTools.permMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)) (i j : Fin n), (j : ℕ) = i + 1 → w⁻¹ i < w⁻¹ j → hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) * hk ρ (iwC k n C) (pm k n w) = hk ρ (iwC k n C) (pm k n (Equiv.swap i j * w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w i j hij hlt
  rw [map_mul]
  have hP := (heckePairIwC k n C).1
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hU : unipO k n ≤ iwC k n C := by
    unfold iwC
    exact le_sup_right.trans le_sup_left
  apply hkMul A _ M ρ _ _ _ hP
  · intro b hb
    obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c :=
      ⟨fun c => (IsLocalRing.residue_surjective c).choose,
        fun c => (IsLocalRing.residue_surjective c).choose_spec⟩
    obtain ⟨x, hx1, hx2, -, hx4⟩ := simpleOrbit k n C i j hij r hr
    obtain ⟨c, b', hb', he⟩ := hx4 b hb
    have hxc : x c ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx2 c
    have hmem : (pm k n w)⁻¹ * x c * pm k n w ∈ unipO k n := by
      unfold unipO
      refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨?_, ?_⟩, ?_⟩
      · intro a b hba
        rw [pm_conj_apply, hx1 c]
        have hab : w a ≠ w b := fun h => (ne_of_lt hba) (w.injective h).symm
        rw [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_neg]
        rintro ⟨h1, h2⟩
        apply absurd hlt
        rw [h1, h2]
        simpa using hba.le
      · intro a
        rw [pm_conj_apply, hx1 c]
        rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
        rintro ⟨h1, h2⟩
        exact hne (h1.trans h2.symm)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (pm_mem_KO k w))
          (Subgroup.mem_inf.1 hxc).2) (pm_mem_KO k w)
    refine ⟨b', hb', (pm k n w)⁻¹ * x c * pm k n w, hU hmem, ?_⟩
    rw [he]
    group
  · rw [← map_mul, permCard, permCard, permCard, ((lenStep n w).1 i j hij).1 hlt]
    have hij' : (1 : Equiv.Perm (Fin n))⁻¹ i < (1 : Equiv.Perm (Fin n))⁻¹ j := by
      rw [inv_one]
      show i < j
      rw [Fin.lt_def]
      omega
    have h1 := ((lenStep n 1).1 i j hij).1 hij'
    rw [mul_one, invLen_one] at h1
    rw [h1]
    ring
end
