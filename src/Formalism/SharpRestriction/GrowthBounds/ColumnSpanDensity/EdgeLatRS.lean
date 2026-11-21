import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfIndex

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

section Dual

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem RS.p_zpow (z : ℤ) : (p : R.Kf) ^ z = algebraMap R.O R.Kf R.w ^ (2 * z) := by
  rw [R.p_eq, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem dual_bases (hD3 : DualHeightBasis) (lamO : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lamO)
    (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ (r : Fin (dimV R.Kf lamO) → Vsp R.Kf lamO) (ρ : Fin (dimV R.Kf lamO) → Module.Dual R.Kf (Vsp R.Kf lamO)),
      (∀ a, r a ∈ Re p R.ι R.σ R.w 1 lamO e) ∧ (∀ a, ρ a ∈ Re' p R.ι R.σ R.w 1 lamO e) ∧
      ∀ a b, be p 1 lamO (r a) (ρ b) = if a = b then 1 else 0 := by
  classical
  obtain ⟨x, π, -, -, -, -, hRe, hRe'⟩ := hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 lamO hdom e he
  refine ⟨fun a => (algebraMap R.O R.Kf R.w ^ (-order 1 lamO (π a))) • x a,
    fun b => (algebraMap R.O R.Kf R.w ^ (-order 1 lamO (π b)) * (p : R.Kf) ^ (-π b)) • x.coord b, ?_, ?_, ?_⟩
  · intro a
    rw [← hRe]
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro b
    rw [← hRe']
    exact Submodule.subset_span ⟨b, rfl⟩
  · intro a b
    unfold be
    rw [LinearMap.smul_apply, map_smul, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, smul_eq_mul, mul_one]
      rw [R.p_zpow, R.p_zpow, ← zpow_add₀ R.w_ne, ← zpow_add₀ R.w_ne, ← zpow_add₀ R.w_ne]
      have : -order 1 lamO (π a) + 2 * -π a + (2 * Ar 1 lamO + -order 1 lamO (π a)) = 0 := by
        unfold order
        ring
      rw [this, zpow_zero]
    · simp [hab]

end Dual

theorem tensor_bound_of_order_bound (hTen : RestTensor) (hOrd : RestOrdBound) (hD3 : DualHeightBasis) (hIncl : DualHeightInclusion) : ResidueClassCount := by
  classical
  intro p n' R m TT ccl aw bw lam0 hBase hDom t c₃ D κ hc hρ e he
  obtain ⟨μ, ν, hν, hHL, hHLe, hdim⟩ := hTen p n' R m TT lam0 hDom
  have hdomO : IsDominant (othW TT lam0) := othW_dom hDom
  have hsmall : ∀ s i, |othW TT lam0 s i| ≤ (ccl : ℤ) := by
    intro s i
    unfold othW
    split_ifs with hs
    · simp
    · exact (hBase s).2 hs i
  set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK
  have hw : wK ≠ 0 := R.w_ne
  obtain ⟨r, ρ, hr, hρm, hrρ⟩ := dual_bases R hD3 (othW TT lam0) hdomO e he
  have hA := Ar_add TT lam0

  have hsrc : ∀ F ∈ CCL R (topW TT lam0) t c₃ e, ∀ a, μ F (r a) ∈ CCL R lam0 (t + (2 * n' * ccl)) (c₃ - (2 * n' * ccl)) e := by
    intro F hF a
    have hr0 := (hOrd p n' R m (othW TT lam0) ccl hdomO hsmall e he).1 (hr a)
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have h1 := mu_scale μ hF.1.1 hr0
      rw [← hHL e.src he.1, ← zpow_add₀ hw] at h1
      have : -(t : ℤ) + -((2 * n' * ccl : ℕ) : ℤ) = -((t + (2 * n' * ccl) : ℕ) : ℤ) := by push_cast; ring
      rwa [this] at h1
    · have h1 := mu_scale μ hF.1.2 (hr a)
      rw [← hHLe e he, ← zpow_add₀ hw] at h1
      have : -Ar 1 (topW TT lam0) + -Ar 1 (othW TT lam0) = -Ar 1 lam0 := by rw [hA]; ring
      rwa [this] at h1
    · rw [Submodule.mem_iInf]
      intro e'
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have hF' := scale_scale_mem (CCL_other R (topW TT lam0) t c₃ e e' h1 h2 h3 hF)
      have hinc := (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 (othW TT lam0) hdomO e' h1).1
      rw [h2] at hinc
      have hr1 := scale_scale_mem (scale_mono _ hinc hr0)
      have h4 := mu_scale μ hF' hr1
      rw [← hHLe e' h1] at h4
      apply mem_scale_scale
      have : wK ^ (c₃ : ℤ) * wK ^ (-Ar 1 (topW TT lam0)) *
          (wK ^ (-((2 * n' * ccl : ℕ) : ℤ)) * wK ^ (-Ar 1 (othW TT lam0))) =
          wK ^ ((c₃ - (2 * n' * ccl) : ℕ) : ℤ) * wK ^ (-Ar 1 lam0) := by
        rw [← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hA, Nat.cast_sub hc]
        congr 1
        ring
      rwa [this] at h4

  have htst : ∀ G ∈ CCL' R (topW TT lam0) t c₃ e, ∀ a, ν G (ρ a) ∈ CCL' R lam0 (t + (2 * n' * ccl)) (c₃ - (2 * n' * ccl)) e := by
    intro G hG a
    have hr0 := (hOrd p n' R m (othW TT lam0) ccl hdomO hsmall e he).2 (hρm a)
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have h1 := nu_scale μ ν hν hG.1.1 hr0
      rw [← hHL e.tgt he.2.1, ← zpow_add₀ hw] at h1
      have : -(t : ℤ) + -((2 * n' * ccl : ℕ) : ℤ) = -((t + (2 * n' * ccl) : ℕ) : ℤ) := by push_cast; ring
      rwa [this] at h1
    · have h1 := nu_scale μ ν hν hG.1.2 (hρm a)
      rw [← hHLe e he, ← zpow_add₀ hw] at h1
      have : -Ar 1 (topW TT lam0) + -Ar 1 (othW TT lam0) = -Ar 1 lam0 := by rw [hA]; ring
      rwa [this] at h1
    · rw [Submodule.mem_iInf]
      intro e'
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have hG' := scale_scale_mem (CCL'_other R (topW TT lam0) t c₃ e e' h1 h2 h3 hG)
      have hinc := (hIncl p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 (othW TT lam0) hdomO e' h1).2
      rw [h2] at hinc
      have hr1 := scale_scale_mem (scale_mono _ hinc hr0)
      have h4 := nu_scale μ ν hν hG' hr1
      rw [← hHLe e' h1] at h4
      apply mem_scale_scale
      have : wK ^ (c₃ : ℤ) * wK ^ (-Ar 1 (topW TT lam0)) *
          (wK ^ (-((2 * n' * ccl : ℕ) : ℤ)) * wK ^ (-Ar 1 (othW TT lam0))) =
          wK ^ ((c₃ - (2 * n' * ccl) : ℕ) : ℤ) * wK ^ (-Ar 1 lam0) := by
        rw [← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hA, Nat.cast_sub hc]
        congr 1
        ring
      rwa [this] at h4

  have hbe : ∀ F G a b, be p 1 lam0 (μ F (r a)) (ν G (ρ b)) =
      be p 1 (topW TT lam0) F G * (if a = b then 1 else 0) := by
    intro F G a b
    rw [← hrρ a b]
    unfold be
    have hp0 : (p : R.Kf) ≠ 0 := by rw [R.p_eq]; exact pow_ne_zero _ hw
    rw [map_smul, hν, map_smul, map_smul, hA, zpow_add₀ hp0]
    simp only [smul_eq_mul]
    ring
  obtain ⟨nT, hnT, hfac⟩ := hρ e he
  refine ⟨nT * (dimV R.Kf (othW TT lam0)), ?_, ?_⟩
  · have h1 : dL R lam0 = dL R (topW TT lam0) * (dimV R.Kf (othW TT lam0)) := by
      unfold dL
      rw [hdim]
      push_cast
      ring
    rw [h1, ← mul_assoc]
    push_cast
    exact mul_le_mul_of_nonneg_right hnT (Nat.cast_nonneg _)
  · rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
    · exact Or.inl (by rw [h0, zero_mul])
    · refine FactorsLE_of_index (I := Fin nT × Fin (dimV R.Kf (othW TT lam0))) (nT * (dimV R.Kf (othW TT lam0))) (by simp)
        (fun i => μ (x i.1) (r i.2)) (fun l => ν (y l.1) (ρ l.2)) (fun i => hsrc _ (hx i.1) i.2)
        (fun l => htst _ (hy l.1) l.2) z (Matrix.of fun l j => if l.2 = j.2 then M l.1 j.1 else 0) hz hv ?_
      rintro ⟨i, a⟩ ⟨j, b⟩
      rw [Fintype.sum_prod_type]
      simp only [hbe, Matrix.of_apply]
      have h2 : ∀ l : Fin nT, ∑ b' : Fin (dimV R.Kf (othW TT lam0)), be p 1 (topW TT lam0) (x i) (y l) * (if a = b' then 1 else 0) *
          algebraMap R.O R.Kf (if b' = b then M l j else 0) =
          if a = b then be p 1 (topW TT lam0) (x i) (y l) * algebraMap R.O R.Kf (M l j) else 0 := by
        intro l
        rw [Finset.sum_eq_single a]
        · by_cases hab : a = b <;> simp [hab]
        · intro b' _ hb'
          simp [Ne.symm hb']
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h2]
      by_cases hab : a = b
      · subst hab
        simp only [if_true]
        rw [hM i j]
        by_cases hij : i = j
        · subst hij; simp
        · have : ((i, a) : Fin nT × Fin (dimV R.Kf (othW TT lam0))) ≠ (j, a) := fun h => hij (Prod.mk.inj h).1
          rw [if_neg hij, if_neg this]
      · have : ((i, a) : Fin nT × Fin (dimV R.Kf (othW TT lam0))) ≠ (j, b) := fun h => hab (Prod.mk.inj h).2
        simp [hab, this]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

theorem P_rev (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w))) :
    (algebraMap O Kf w ^ (-(((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) *
      lam (Fin.last m)))) • F ∈ nablaLTw O Kf m lam g := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set ν : Fin (m + 1) → ℕ := fun t => (lam t - lam (Fin.last m)).toNat with hν
  set e : ℤ := lam (Fin.last m) with he
  obtain ⟨b, hb, -⟩ := lb_basis O (m + 1) (m + 1) ν
  set t : Fin (m + 1) → Kf := fun a => if a.val < r then c⁻¹ else 1 with ht
  have ht0 : ∀ a, t a ≠ 0 := by
    intro a
    simp only [ht]
    split_ifs
    · exact inv_ne_zero hw
    · exact one_ne_zero
  have hB := (nablaLBasis O Kf hinj (m + 1) (m + 1) ν b _ hb g hg).2
  have hD := (nablaLDiag O Kf hinj (m + 1) (m + 1) ν b _ hb g t hg ht0).2
  have hle : nablaL O Kf (m + 1) (m + 1) ν (g * Matrix.diagonal t) ≤ nablaL O Kf (m + 1) (m + 1) ν g := by
    rw [← hD, ← hB, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    set Fi := rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hFi
    set π' : ℕ := ∑ a : Fin (m + 1) with a.val < r, rowWt i.1 a with hπ
    have h2 : ∏ a, t a ^ rowWt i.1 a = (c⁻¹) ^ π' := by
      rw [hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      simp only [ht]
      split_ifs <;> simp
    have h6 : ((c⁻¹) ^ π')⁻¹ = c ^ π' := by rw [inv_pow, inv_inv]
    show (∏ a, t a ^ rowWt i.1 a)⁻¹ • Fi ∈ _
    rw [h2, h6, hc, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨F0, hF0, rfl⟩ := hF
  refine ⟨F0, hle hF0, ?_⟩
  set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
  show g.det ^ (-e) • F0 = c ^ (-((ρ : ℤ) * e)) • ((g * lb_D (m + 1) r c).det ^ (-e) • F0)
  have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
    rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
    rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
  rw [smul_smul, h1, mul_zpow, h5, mul_comm (g.det ^ (-e)), ← mul_assoc, ← zpow_add₀ hw, neg_add_cancel, zpow_zero,
    one_mul]

theorem zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ H0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w)))) :
    (algebraMap O Kf w ^ (-(((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) *
      lam (Fin.last m)))) • F ∈ H0 O m lam (colSpan O g) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold H0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  have h1 : F ∈ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) :=
    (iInf₂_le _ ⟨hgD, rfl⟩ : _ ≤ nablaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w))) hF
  have h2 := P_rev O Kf hinj m r lam w hw g hg F h1
  exact (le_iInf₂ fun h hh => lb_indep O Kf hinj m lam _ h hg hh.1 hh.2 : nablaLTw O Kf m lam g ≤ _) h2

section RSLat

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem extO_RS (s : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) R.Qq) :
    extO R.O R.ι R.σ s (colSpan R.W g) = colSpan R.O (la_tw R.ι R.σ s g) :=
  la_extO R.ι R.σ R.jO (fun x => by obtain ⟨y, hy⟩ := R.std.1.frob x; exact ⟨_, hy⟩) R.std.1.ι_comp s g

theorem tw_p (s : ℕ) {k : ℕ} (x : Fin k → R.Qq) (i : Fin k) :
    twistVec R.ι R.σ s ((p : R.W) • x) i = (p : R.Kf) * R.ι ((R.σ ^ s) (x i)) := by
  show R.ι ((R.σ ^ s) ((p : R.W) • x i)) = _
  rw [Algebra.smul_def, map_natCast, map_mul, map_mul, map_natCast, map_natCast]

theorem edgeLat_RS (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) :
    ∃ gs : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf, (∀ s, IsUnit (gs s).det) ∧
      (∀ s, extO R.O R.ι R.σ s e.src = colSpan R.O (gs s)) ∧
      (∀ s, LeAt p R.ι R.σ R.w s e = colSpan R.O (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w))) ∧
      (∀ s, extO R.O R.ι R.σ s e.tgt =
        colSpan R.O (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w) * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w))) := by
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  unfold lb_D
  set c : R.Kf := algebraMap R.O R.Kf R.w with hc
  have hw : c ≠ 0 := R.w_ne
  have hpK : (p : R.Kf) = c ^ 2 := R.p_eq
  have hpK0 : (p : R.Kf) ≠ 0 := by rw [hpK]; exact pow_ne_zero _ hw
  have hpQ0 : (p : R.Qq) ≠ 0 := by
    intro h0
    apply hpK0
    have := congrArg R.ι h0
    simpa using this
  set dK : Fin (m + 1) → R.Kf := fun a => if a.val < 1 then c⁻¹ else 1 with hdK
  set dQ : Fin (m + 1) → R.Qq := fun a => if a.val < 1 then ((p : R.Qq))⁻¹ else 1 with hdQ
  have hDD : ∀ s, la_tw R.ι R.σ s (g * Matrix.diagonal dQ) =
      la_tw R.ι R.σ s g * Matrix.diagonal dK * Matrix.diagonal dK := by
    intro s
    ext i j
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.mul_diagonal, lb_tw_apply, lb_tw_apply,
      Matrix.mul_diagonal, map_mul, map_mul]
    congr 1
    simp only [hdQ, hdK]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast, hpK, pow_two, mul_inv]
    · simp
  have e1 : ∀ s, extO R.O R.ι R.σ s e.src = colSpan R.O (la_tw R.ι R.σ s g) :=
    fun s => by rw [hsrc]; exact extO_RS R s g
  have e3 : ∀ s, extO R.O R.ι R.σ s e.tgt =
      colSpan R.O (la_tw R.ι R.σ s g * Matrix.diagonal dK * Matrix.diagonal dK) :=
    fun s => by rw [htgt, extO_RS R, hDD]
  refine ⟨fun s => la_tw R.ι R.σ s g, fun s => la_tw_det _ _ s g hg, e1, ?_, e3⟩
  intro s
  set gK := la_tw R.ι R.σ s g with hgK
  apply le_antisymm
  · unfold LeAt
    refine sup_le ?_ ?_
    · rw [e1]
      intro x hx
      have h1 : gK = gK * Matrix.diagonal dK *
          Matrix.diagonal (fun a : Fin (m + 1) => if a.val < 1 then c else 1) := by
        rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
        have h2 : (fun a : Fin (m + 1) => dK a * (if a.val < 1 then c else 1)) = fun _ => 1 := by
          funext a
          simp only [hdK]
          split_ifs
          · exact inv_mul_cancel₀ hw
          · simp
        rw [h2, Matrix.diagonal_one, Matrix.mul_one]
      have hx' : x ∈ colSpan R.O gK := hx
      rw [h1] at hx'
      have h3 := lb_col (gK * Matrix.diagonal dK) _
        (fun a : Fin (m + 1) => if a.val < 1 then R.w else 1) 1
        (by intro j; split_ifs <;> simp [hc]) x hx'
      rw [one_smul] at h3
      exact h3
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : c⁻¹ • twistVec R.ι R.σ s ((p : R.W) • x) =
          R.w • twistVec R.ι R.σ s x := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, tw_p R, smul_eq_mul, Algebra.smul_def, ← hc, hpK]
        show c⁻¹ * (c ^ 2 * _) = c * R.ι ((R.σ ^ s) (x i))
        field_simp
      have h2 : twistVec R.ι R.σ s x ∈
          colSpan R.O (gK * Matrix.diagonal dK * Matrix.diagonal dK) := by
        rw [← e3]; exact Submodule.subset_span ⟨x, hx, rfl⟩
      show c⁻¹ • twistVec R.ι R.σ s ((p : R.W) • x) ∈ _
      rw [h1]
      exact lb_col (gK * Matrix.diagonal dK) dK
        (fun a : Fin (m + 1) => if a.val < 1 then 1 else R.w) R.w
        (by
          intro j
          simp only [hdK]
          split_ifs
          · rw [← hc, mul_inv_cancel₀ hw, map_one]
          · rw [mul_one]) _ h2
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold LeAt
    by_cases hj : j.val < 1
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      refine ⟨fun i => (g * Matrix.diagonal dQ) i j, ?_, ?_⟩
      · rw [htgt]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        show c⁻¹ • twistVec R.ι R.σ s
          ((p : R.W) • fun i => (g * Matrix.diagonal dQ) i j) i = (gK * Matrix.diagonal dK) i j
        rw [tw_p R, Matrix.mul_diagonal, Matrix.mul_diagonal, smul_eq_mul, hgK, lb_tw_apply]
        simp only [hdQ, hdK, hj, if_true, map_mul, map_inv₀, map_natCast]
        field_simp
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨fun i => g i j, ?_, ?_⟩
      · rw [hsrc]; exact Submodule.subset_span ⟨j, rfl⟩
      · funext i
        simp only [twistVec, Matrix.mul_diagonal, hdK, hj, if_false, mul_one, lb_tw_apply]

end RSLat

end Formalism.MainNotions.flipOneThree.Pf

end
end
