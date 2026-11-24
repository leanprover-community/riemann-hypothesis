module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation

@[expose] public section

namespace Bl.general_b_fact_upper_bis

theorem goal1 {A K : Type} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (w : IsDedekindDomain.HeightOneSpectrum A)
    {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K V) {O Kf Fn : Type}
    [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup Fn] [Module Kf Fn] [Module O Fn]
    [IsScalarTower O Kf Fn] (φ : K →+* Kf) (cmp : V →+ Fn)
    (h1 : ∀ x : K, w.valuation K x ≤ 1 ↔ φ x ∈ Set.range (algebraMap O Kf))
    (h2 : ∀ (a : K) (x : V), cmp (a • x) = φ a • cmp x)
    (h3 : LinearIndependent Kf fun a : ι => cmp (b a))
    (Lat : Submodule A V) (hLat : Lat.FG) (v : V)
    (hv : cmp v ∈ Submodule.span O (cmp '' (Lat : Set V))) :
    ∃ s : A, s ∉ w.asIdeal ∧ s • v ∈ Lat := by
  classical
  have T : ∀ f : V →ₗ[K] K, ∃ g : Fn →ₗ[Kf] Kf, ∀ y, g (cmp y) = φ (f y) := fun f => by
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span h3).constr Kf fun i => φ (f (b i)))
    refine ⟨g, fun y => ?_⟩
    have hb : ∀ i, g (cmp (b i)) = φ (f (b i)) := fun i => by
      have := congrArg (fun F => F (Module.Basis.span h3 i)) hg
      simp only [Module.Basis.constr_basis] at this
      simpa using this
    rw [← b.sum_repr y]
    simp only [map_sum, h2, map_smul, smul_eq_mul, hb, map_mul]
  have hsm : ∀ c : K, w.valuation K c ≤ 1 → ∀ (Tt : Set Fn) (z : Fn),
      z ∈ Submodule.span O Tt → φ c • z ∈ Submodule.span O Tt := fun c hc Tt z hz => by
    obtain ⟨o, ho⟩ := (h1 c).1 hc
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o hz
  have hred : ∀ n : ℕ, ∀ S : Finset V, S.card = n → ∃ S' ⊆ S,
      LinearIndependent K ((↑) : S' → V) ∧
      Submodule.span O (cmp '' (S : Set V)) ≤ Submodule.span O (cmp '' (S' : Set V)) := fun n => by
    refine Nat.strong_induction_on n fun n ih S hSn => ?_
    by_cases hli : LinearIndependent K ((↑) : S → V)
    · exact ⟨S, Finset.Subset.rfl, hli, le_rfl⟩
    · rw [Fintype.not_linearIndependent_iff] at hli
      obtain ⟨lam, hlam, x1, hx1ne⟩ := hli
      obtain ⟨x0, -, hmax⟩ :=
        Finset.univ.exists_max_image (fun x : S => w.valuation K (lam x)) ⟨x1, Finset.mem_univ _⟩
      have hl0 : lam x0 ≠ 0 := fun h0 => by
        have h01 := hmax x1 (Finset.mem_univ _)
        simp [h0, hx1ne] at h01
      have hrel : (x0 : V) = ∑ x ∈ Finset.univ.erase x0, (-(lam x0)⁻¹ * lam x) • (x : V) := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x0)] at hlam
        simp only [neg_mul, neg_smul, mul_smul, Finset.sum_neg_distrib, ← Finset.smul_sum,
          eq_neg_of_add_eq_zero_right hlam, smul_neg, neg_neg, inv_smul_smul₀ hl0]
      have hx0mem : cmp x0 ∈ Submodule.span O (cmp '' (S.erase x0 : Set V)) := by
        rw [congrArg cmp hrel, map_sum]
        refine Submodule.sum_mem _ fun x hx => ?_
        rw [h2]
        refine hsm _ ?_ _ _ (Submodule.subset_span ⟨x, Finset.mem_coe.2
          (Finset.mem_erase.2 ⟨Subtype.coe_ne_coe.2 (Finset.ne_of_mem_erase hx), x.2⟩), rfl⟩)
        rw [map_mul, Valuation.map_neg, map_inv₀,
          inv_mul_le_one₀ (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 hl0))]
        exact hmax x (Finset.mem_univ _)
      have hstep : Submodule.span O (cmp '' (S : Set V)) ≤
          Submodule.span O (cmp '' (S.erase x0 : Set V)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨y, hy, rfl⟩
        by_cases hyx : y = x0
        · exact hyx ▸ hx0mem
        · exact Submodule.subset_span ⟨y, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hyx, hy⟩), rfl⟩
      obtain ⟨S', hS'sub, hS'li, hS'le⟩ :=
        ih _ (hSn ▸ Finset.card_erase_lt_of_mem x0.2) (S.erase x0) rfl
      exact ⟨S', hS'sub.trans (Finset.erase_subset _ _), hS'li, hstep.trans hS'le⟩
  obtain ⟨S, hS⟩ := hLat
  have hle : Submodule.span O (cmp '' (Lat : Set V)) ≤ Submodule.span O (cmp '' (S : Set V)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span A (S : Set V) := hS ▸ hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul K a x, h2]
      exact hsm _ (w.valuation_le_one (K := K) a) _ _ hx
  obtain ⟨S', hS'sub, hli, hS'le⟩ := hred S.card S rfl
  have hv' : cmp v ∈ Submodule.span O (Set.range fun x : S' => cmp x) := by
    convert hS'le (hle hv) using 2
    ext; simp
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hv'
  have hvK : v ∈ Submodule.span K (Set.range ((↑) : S' → V)) := by
    by_contra hnv
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_notMem hnv
    obtain ⟨g, hg⟩ := T f
    have hgv : g (cmp v) = 0 := by
      rw [← ho, map_sum]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← algebraMap_smul Kf, map_smul, hg,
        LinearMap.mem_ker.1 (hker (Submodule.subset_span ⟨x, rfl⟩)), map_zero, smul_zero]
    exact hf0 ((map_eq_zero φ).1 ((hg v).symm.trans hgv))
  let bs := Module.Basis.span hli
  let c : S' → K := bs.repr ⟨v, hvK⟩
  have hwc : ∀ x : S', w.valuation K (c x) ≤ 1 := fun x => (h1 (c x)).2 ⟨o x, by
    obtain ⟨f, hf⟩ := LinearMap.exists_extend (bs.coord x)
    obtain ⟨g, hg⟩ := T f
    have hfv : f v = c x := congrArg (fun F => F ⟨v, hvK⟩) hf
    have hfy : ∀ y : S', f y = if y = x then 1 else 0 := fun y => by
      have := congrArg (fun F => F (bs y)) hf
      simpa [bs, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm] using this
    have e := hg v
    rw [hfv, ← ho, map_sum] at e
    simp_rw [← algebraMap_smul (R := O) Kf] at e
    simp only [map_smul, hg, hfy, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e
    exact e⟩
  choose nn d hnd using fun x : S' => w.exists_primeCompl_mul_eq_of_integer (c x) (hwc x)
  refine ⟨∏ x : S', (d x : A), w.asIdeal.primeCompl.prod_mem fun x _ => (d x).2, ?_⟩
  have hvsum : v = ∑ x : S', c x • (x : V) := by
    simpa [c, bs] using (congrArg Subtype.val (bs.sum_repr ⟨v, hvK⟩)).symm
  rw [hvsum, Finset.smul_sum, ← hS]
  refine Submodule.sum_mem _ fun x _ => ?_
  have hterm : (∏ y : S', (d y : A)) • (c x • (x : V)) =
      ((∏ y ∈ Finset.univ.erase x, (d y : A)) * nn x) • (x : V) := by
    rw [← algebraMap_smul K (∏ y : S', (d y : A)), smul_smul,
      ← algebraMap_smul K ((∏ y ∈ Finset.univ.erase x, (d y : A)) * nn x),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
      map_mul, map_mul, ← hnd x]
    congr 1; ring
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (hS'sub x.2)))

end Bl.general_b_fact_upper_bis
