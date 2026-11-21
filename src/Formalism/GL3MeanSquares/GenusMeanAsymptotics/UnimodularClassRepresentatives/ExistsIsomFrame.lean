import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormOneOfPair
import Formalism.HermitianLattices.StatementLat

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def quasiRefl (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - a • (h u).smulRight u

theorem quasiRefl_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  first
  | simp [quasiRefl, smul_smul]
  | rw [quasiRefl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, smul_smul]

theorem quasiRefl_comp (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
  rw [sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]
  left
  linear_combination (h u v) * hab

theorem quasiRefl_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by
  have hsym : star (h u v) = h v u := by
    have := hs.eq u v
    simpa [starRingEnd_apply] using this
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_mul, hsym, RingHom.id_apply]
  linear_combination (-(h v u * h u w)) * ha

theorem exists_isom_fix {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    {x y : V} (hx : h x x = 1) (hy : h y y = 1) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ ∀ v, h x v = 0 → h y v = 0 → τ v = v := by
  have hsym : ∀ p q : V, star (h p q) = h q p := fun p q => by
    have := hs.eq p q
    simpa [starRingEnd_apply] using this
  by_cases hyx : h y x = 1
  · have hxy : h x y = 1 := by rw [← hsym, hyx, star_one]
    have hu : h (x - y) (x - y) = 0 := by
      simp only [map_sub, LinearMap.sub_apply, hx, hy, hxy, hyx]; ring
    have hxy' : x = y := sub_eq_zero.mp (hd _ hu)
    subst hxy'
    exact ⟨1, one_mem _, rfl, fun v _ _ => rfl⟩
  · have hp : (1 : K) - h y x ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
    have hq : (1 : K) - h x y ≠ 0 := by
      intro h0
      apply hp
      have := congrArg star h0
      rw [star_sub, star_one, hsym, star_zero] at this
      exact this
    have huu : h (x - y) (x - y) = (1 - h y x) + (1 - h x y) := by
      simp only [map_sub, LinearMap.sub_apply, hx, hy]; ring
    have hux : h (x - y) x = 1 - h y x := by
      simp only [map_sub, LinearMap.sub_apply, hx]
    have hsa : star ((1 - h y x)⁻¹) = (1 - h x y)⁻¹ := by
      first
      | rw [star_inv₀, star_sub, star_one, hsym]
      | rw [star_inv', star_sub, star_one, hsym]
    have e1 : (1 - h y x)⁻¹ * (1 - h y x) = 1 := inv_mul_cancel₀ hp
    have e2 : (1 - h x y)⁻¹ * (1 - h x y) = 1 := inv_mul_cancel₀ hq
    have ha : (1 - h y x)⁻¹ + star ((1 - h y x)⁻¹) =
        (1 - h y x)⁻¹ * star ((1 - h y x)⁻¹) * h (x - y) (x - y) := by
      rw [hsa, huu]
      linear_combination (-(1 - h x y)⁻¹) * e1 - (1 - h y x)⁻¹ * e2
    have hb : star ((1 - h y x)⁻¹) + (1 - h y x)⁻¹ =
        star ((1 - h y x)⁻¹) * (1 - h y x)⁻¹ * h (x - y) (x - y) := by
      rw [add_comm, mul_comm (star _) _]; exact ha
    refine ⟨LinearEquiv.ofLinear (quasiRefl h (x - y) ((1 - h y x)⁻¹))
      (quasiRefl h (x - y) (star ((1 - h y x)⁻¹))) (quasiRefl_comp h (x - y) ha)
      (quasiRefl_comp h (x - y) hb), ?_, ?_, ?_⟩
    · first
      | exact fun v w => quasiRefl_isom hs (x - y) ha v w
      | (intro v w; exact quasiRefl_isom hs (x - y) ha v w)
      | (show ∀ v w, _ = _; intro v w; exact quasiRefl_isom hs (x - y) ha v w)
    · show quasiRefl h (x - y) ((1 - h y x)⁻¹) x = y
      rw [quasiRefl_apply, hux, inv_mul_cancel₀ hp, one_smul, sub_sub_cancel]
    · intro v h1 h2
      show quasiRefl h (x - y) ((1 - h y x)⁻¹) v = v
      rw [quasiRefl_apply, map_sub, LinearMap.sub_apply, h1, h2, sub_zero, mul_zero, zero_smul, sub_zero]

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

structure IsSelfDualMod (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) : Prop where
  smul_mem : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M
  int : ∀ x ∈ M, ∀ y ∈ M, h x y ∈ S
  dual : ∀ x : V, (∀ m ∈ M, h m x ∈ S) → x ∈ M
  span : ∀ x : V, ∃ t : K, t ≠ 0 ∧ t • x ∈ M

variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem exists_next (hS : IsHermSemilocal S) (hs : h.IsSymm) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (hx : ∀ i j, h (x i) (x j) = if i = j then 1 else 0)
    (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M) (j : ι) (hj : j ∉ s) :
    ∃ z ∈ M, h z z = 1 ∧ ∀ i ∈ s, h (x i) z = 0 := by
  have hl : ∀ (c : K) (u w : V), h (c • u) w = star c * h u w := by
    intro c u w
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  have hr : ∀ (c : K) (u w : V), h u (c • w) = c * h u w := by
    intro c u w
    simp
  have hsym : ∀ u w : V, star (h u w) = h w u := by
    intro u w
    have hsu := hs.eq u w
    rwa [starRingEnd_apply] at hsu
  have hxx : h (x j) (x j) = 1 := by
    rw [hx]
    simp
  have hxj : ∀ i ∈ s, h (x i) (x j) = 0 := by
    intro i hi
    have hij : i ≠ j := fun e => hj (e ▸ hi)
    rw [hx]
    simp [hij]
  have hjx : ∀ i ∈ s, h (x j) (x i) = 0 := by
    intro i hi
    rw [← hsym, hxj i hi, star_zero]
  obtain ⟨t, ht0, htM⟩ := hM.span (x j)
  have hmemA : ∀ a : K, a ∈ M.map (h (x j)).toAddMonoidHom ↔ ∃ m ∈ M, h (x j) m = a := by
    intro a
    rw [AddSubgroup.mem_map]
    rfl
  obtain ⟨α, hαA, hα0, hαS⟩ := hS.principal (M.map (h (x j)).toAddMonoidHom)
    (by
      intro r hr' a ha
      obtain ⟨m, hm, rfl⟩ := (hmemA a).1 ha
      exact (hmemA _).2 ⟨r • m, hM.smul_mem r hr' m hm, hr r _ _⟩)
    ⟨t, (hmemA t).2 ⟨t • x j, htM, by rw [hr, hxx, mul_one]⟩, ht0⟩
    ⟨star t, star_ne_zero.2 ht0, fun a ha => by
      obtain ⟨m, hm, rfl⟩ := (hmemA a).1 ha
      rw [← hl]
      exact hM.int _ htM m hm⟩
  obtain ⟨w1, hw1M, hw1⟩ := (hmemA α).1 hαA
  obtain ⟨a2, ha2⟩ : ∃ a2 : K, a2 = star α⁻¹ := ⟨_, rfl⟩
  have ha20 : a2 ≠ 0 := by
    rw [ha2]
    exact star_ne_zero.2 (inv_ne_zero hα0)
  have hvM : a2 • x j ∈ M := by
    apply hM.dual
    intro m hm
    rw [hr, ← hsym]
    have h1 := hS.star_mem _ (hαS _ ((hmemA _).2 ⟨m, hm, rfl⟩))
    rw [star_mul', ← ha2, mul_comm] at h1
    exact h1
  have hcM : ∀ i ∈ s, (h (x i) w1) • x i ∈ M := fun i hi =>
    hM.smul_mem _ (hM.int _ (hxM i hi) _ hw1M) _ (hxM i hi)
  have hw0M : w1 - ∑ i ∈ s, (h (x i) w1) • x i ∈ M :=
    M.sub_mem hw1M (M.sum_mem hcM)
  have hw0o : ∀ k ∈ s, h (x k) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 0 := by
    intro k hk
    rw [map_sub, map_sum]
    simp only [hr, hx]
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', hk]
  have hvw : h (a2 • x j) (w1 - ∑ i ∈ s, (h (x i) w1) • x i) = 1 := by
    rw [map_sub, map_sum, Finset.sum_eq_zero, sub_zero, hl, hw1, ha2, star_star,
      inv_mul_cancel₀ hα0]
    intro i hi
    rw [hr, hl, hjx i hi, mul_zero, mul_zero]
  have hvvS : star a2 * a2 ∈ S := by
    have := hM.int _ hvM _ hvM
    rwa [hl, hr, hxx, mul_one] at this
  obtain ⟨b, hb1, hbS⟩ := exists_norm_one_mul_mem hS hvvS
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb1
  obtain ⟨c, hc, d, hd, hcd⟩ := exists_norm_one_of_pair hS hs (y := b • a2 • x j)
    (w := b • (w1 - ∑ i ∈ s, (h (x i) w1) • x i)) (a := a2 * b) hbS (mul_ne_zero ha20 hb0)
    (by rw [hl, hr, hl, hr, hxx, star_mul']; ring)
    (by rw [hl, hr, hvw, mul_one, hb1])
    (by rw [hl, hr, ← mul_assoc, hb1, one_mul]; exact hM.int _ hw0M _ hw0M)
  refine ⟨c • (w1 - ∑ i ∈ s, (h (x i) w1) • x i) + d • a2 • x j,
    M.add_mem (hM.smul_mem c hc _ hw0M) (hM.smul_mem d hd _ hvM), ?_, ?_⟩
  · rw [smul_comm c b, smul_comm d b, ← smul_add, hl, hr, ← mul_assoc, hb1, one_mul] at hcd
    exact hcd
  · intro i hi
    rw [map_add, hr, hr, hw0o i hi, hr, hxj i hi]
    simp

theorem exists_isom_frame (hS : IsHermSemilocal S) (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsSelfDualMod S h M) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (e i) ∈ M := by
  have hsym : ∀ u w : V, star (h u w) = h w u := by
    intro u w
    have hsu := hs.eq u w
    rwa [starRingEnd_apply] at hsu
  have key : ∀ k : ℕ, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, (i : ℕ) < k → g (e i) ∈ M := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨1, (Formalism.HermitianLatticesTheory.isom h).one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (Nat.le_of_succ_le hk)
      have hgi : ∀ u w : V, h (g u) (g w) = h u w := hg
      obtain ⟨kk, hkk⟩ : ∃ kk : Fin n, (kk : ℕ) = k := ⟨⟨k, Nat.lt_of_succ_le hk⟩, rfl⟩
      have hxx : ∀ i j : Fin n, h (g (e i)) (g (e j)) = if i = j then 1 else 0 := by
        intro i j
        rw [hgi, he]
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_next hS hs hM (fun i => g (e i)) hxx
        (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k))
        (fun i hi => hgM i (Finset.mem_filter.1 hi).2) kk (by simp [hkk])
      have hzo' : ∀ i : Fin n, (i : ℕ) < k → h (g (e i)) z = 0 := fun i hi =>
        hzo i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      have hk1 : h (g (e kk)) (g (e kk)) = 1 := by
        rw [hxx]
        simp
      obtain ⟨τ, hτ, hτk, hτfix⟩ := exists_isom_fix hs hd hk1 hzz
      refine ⟨τ * g, (Formalism.HermitianLatticesTheory.isom h).mul_mem hτ hg, ?_⟩
      intro i hi
      show τ (g (e i)) ∈ M
      rcases Nat.lt_or_ge (i : ℕ) k with hlt | hge
      · have h1 : h (g (e kk)) (g (e i)) = 0 := by
          rw [hxx]
          have hne : kk ≠ i := by
            intro h'
            rw [← h', hkk] at hlt
            exact lt_irrefl _ hlt
          simp [hne]
        have h2 : h z (g (e i)) = 0 := by
          rw [← hsym, hzo' i hlt, star_zero]
        rw [hτfix _ h1 h2]
        exact hgM i hlt
      · have hik : i = kk := Fin.ext (by omega)
        rw [hik, hτk]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := key n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩

end Formalism.HermitianLattices.Ext.L3.WA
end
end
