import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeWt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem bhw_Ecc_Eab (hE : IsGlRep E) {μ : Fin n → ℝ} {v : D} (hv : ∀ c, E c c v = ((μ c : ℝ) : ℂ) • v)
    (a b : Fin n) (c : Fin n) : E c c (E a b v) = (((μ + root a b) c : ℝ) : ℂ) • E a b v := by
  have h : E c c (E a b v) - E a b (E c c v) =
      (if c = a then E c b else 0) v - (if b = c then E a c else 0) v :=
    LinearMap.congr_fun (hE c c a b) v
  rw [sub_eq_iff_eq_add.mp h, hv c, map_smul]
  rcases eq_or_ne c a with h1 | h1 <;> rcases eq_or_ne c b with h2 | h2
  · subst h1; subst h2; simp [root]
  · subst h1; simp [root, Pi.single_apply, Ne.symm h2, h2, add_smul, add_comm]
  · subst h2; simp [root, Pi.single_apply, h1, sub_smul, add_smul]; exact add_comm _ _
  · simp [root, Pi.single_apply, h1, h2, Ne.symm h2]

private theorem hasDerivAt_zero_mem_of_forall_mem_finiteDim {S : Submodule ℂ H} [FiniteDimensional ℂ S] {f : ℝ → H} {L : H}
    (hf : HasDerivAt f L 0) (hS : ∀ t, f t ∈ S) : L ∈ S := by
  have hc : IsClosed (S : Set H) := Submodule.closed_of_finiteDimensional S
  refine hc.mem_of_tendsto hf.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
  rw [zero_add]
  exact Submodule.smul_of_tower_mem S t⁻¹ (S.sub_mem (hS t) (hS 0))

private theorem exp_real_smul_mem_Kset_of_skewHermitian_commute_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (hJ : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.REAL.Kset ε := by
  have hsk : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
    rw [Matrix.conjTranspose_smul, hX]; simp
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hsk,
      ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl ((t : ℂ) • X)))]
    simp
  · exact (Commute.exp_left (Commute.smul_left hJ (t : ℂ))).eq

private theorem inG_of_conjTranspose_eq_neg_commute_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (hJ : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : inG ε X := by
  have hJJ : Jm ε = Formalism.REAL.Jm ε := rfl
  show Xᴴ * Jm ε + Jm ε * X = 0
  rw [hJJ, hX, neg_mul, hJ]
  simp

private theorem commute_Jm_of_support_same_sign (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i j, X i j ≠ 0 → ε i = ε j) : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
  ext i j
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : X i j = 0
  · simp [h]
  · rw [hX i j h]; ring

private theorem E_mem_of_isKStableOn_of_same_sign (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ H} [FiniteDimensional ℂ S]
    (hS : Formalism.MainNotions.S.IsKStableOn ε σ S) (a b : Fin n) (he : ε a = ε b) (w : D) (hw : (w : H) ∈ S) :
    ((E a b w : D) : H) ∈ S := by
  have gen : ∀ c : ℂ, (((c • E a b - star c • E b a) w : D) : H) ∈ S := by
    intro c
    have hsk : (Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0) : Matrix (Fin n) (Fin n) ℂ)ᴴ =
        -(Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.neg_apply]
      split_ifs <;> simp
    have hcm := commute_Jm_of_support_same_sign ε (Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0)) (by
      intro i j h
      simp only [Matrix.of_apply] at h
      split_ifs at h <;> simp_all)
    have hact : actM E (Matrix.of fun i j => (if i = a then (if j = b then c else 0) else 0) -
        (if i = b then (if j = a then star c else 0) else 0)) = c • E a b - star c • E b a := by
      have key : ∀ (p q : Fin n) (d : ℂ),
          (∑ i, ∑ j, (if i = p then (if j = q then d else 0) else 0) • E i j) = d • E p q := by
        intro p q d
        rw [Finset.sum_eq_single p (fun i _ hi => by simp [hi]) (by simp),
          Finset.sum_eq_single q (fun j _ hj => by simp [hj]) (by simp)]
        simp
      simp only [actM, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [key, key]
    rw [← hact]
    exact hasDerivAt_zero_mem_of_forall_mem_finiteDim (hD.deriv _ (inG_of_conjTranspose_eq_neg_commute_Jm ε _ hsk hcm) w)
      (fun t => hS _ (exp_real_smul_mem_Kset_of_skewHermitian_commute_Jm ε _ hsk hcm t) _ hw)
  have h1 := gen 1
  have hI := gen Complex.I
  have h2 : ((((2 * Complex.I) • E a b w : D)) : H) ∈ S := by
    have : (2 * Complex.I) • E a b w =
        Complex.I • ((((1 : ℂ) • E a b - star (1 : ℂ) • E b a) w)) +
          (Complex.I • E a b - star Complex.I • E b a) w := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, star_one, one_smul,
        Complex.star_def, Complex.conj_I, neg_smul, sub_neg_eq_add, smul_sub]
      rw [two_mul, add_smul]
      abel
    rw [this, Submodule.coe_add, Submodule.coe_smul]
    exact S.add_mem (S.smul_mem _ h1) hI
  rw [Submodule.coe_smul] at h2
  exact (Submodule.smul_mem_iff S (by simp [Complex.I_ne_zero])).1 h2

private theorem not_CDom_add_root_of_lt (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) (hab : a < b)
    (h : Formalism.MainNotions.S.CDom ε (μ + root a b) μ) : False := by
  obtain ⟨c, hc, hsum⟩ := h
  rw [sub_add_cancel_left] at hsum
  have hr : ∀ i j : Fin n, ∑ k : Fin n, ((k : ℕ) : ℝ) * (Formalism.REAL.root i j) k =
      ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
    intro i j
    simp [Formalism.REAL.root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hL : ∑ k : Fin n, ((k : ℕ) : ℝ) * (-(root a b)) k = ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hR : ∑ k : Fin n, ((k : ℕ) : ℝ) * (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) k =
      ∑ i, ∑ j, (c i j : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hr i j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1 : ∑ k : Fin n, ((k : ℕ) : ℝ) * (-(root a b)) k =
      ∑ k : Fin n, ((k : ℕ) : ℝ) * (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) k := by
    rw [hsum]
  rw [hL, hR] at h1
  have hle : ∑ i, ∑ j, (c i j : ℝ) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases h0 : c i j = 0
    · simp [h0]
    · have hij : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
      have hcn : (0 : ℝ) ≤ (c i j : ℝ) := Nat.cast_nonneg _
      nlinarith
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem exists_isKHWVec_of_isKTypeOf (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) (hSD : S ≤ D) :
    ∃ w : D, (w : H) ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w := by
  obtain ⟨hfd, hst, -, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  haveI : FiniteDimensional ℂ S := hfd
  have hwt := (isWtOn_iff hσ hD ⟨v, hSD hvS⟩ μ).1 hvw
  refine ⟨⟨v, hSD hvS⟩, hvS, ?_, fun a => hwt a, fun a b hab he => ?_⟩
  · intro h
    apply hv0
    simpa using congrArg (fun x : D => (x : H)) h
  · by_contra hne
    have huS : ((E a b ⟨v, hSD hvS⟩ : D) : H) ∈ S := E_mem_of_isKStableOn_of_same_sign hD hst a b he _ hvS
    have hu0 : ((E a b ⟨v, hSD hvS⟩ : D) : H) ≠ 0 := fun h => hne (by simpa using h)
    have huw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (μ + root a b) ((E a b ⟨v, hSD hvS⟩ : D) : H) :=
      (isWtOn_iff hσ hD _ (μ + root a b)).2 (fun c => bhw_Ecc_Eab hD.glRep hwt a b c)
    exact not_CDom_add_root_of_lt ε μ a b hab (hdom _ _ huS hu0 huw)

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem kType_map_of_inj {μ : Fin n → ℝ} {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ μ S)
    (f : H →ₗ[ℂ] H) (hf : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, f (σ k x) = σ k (f x))
    (hinj : ∀ x ∈ S, f x = 0 → x = 0) : Formalism.MainNotions.S.IsKTypeOf ε σ μ (S.map f) := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hwt⟩ := hS
  have hwt' : ∀ x ∈ S, ∀ ν, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν (f x) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν x := by
    intro x hx ν h θ hθ
    have h1 := h θ hθ
    rw [← hf _ hθ, ← map_smul] at h1
    have := hinj _ (S.sub_mem (hst _ hθ x hx) (S.smul_mem _ hx)) (by rw [map_sub, h1, sub_self])
    exact sub_eq_zero.1 this
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst g hg x hx, hf g hg x⟩
  · intro S' hS' hK
    let T : Submodule ℂ H := S ⊓ S'.comap f
    have hT : Formalism.MainNotions.S.IsKStableOn ε σ T := fun g hg x hx =>
      ⟨hst g hg x hx.1, by
        show f (σ g x) ∈ S'
        rw [hf g hg]
        exact hK g hg _ hx.2⟩
    rcases hirr T inf_le_left hT with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hS' hy
      have hxT : x ∈ T := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at hxT
      rw [hxT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxT : x ∈ T := by rw [h]; exact hx
      exact hxT.2
  · refine ⟨f v, Submodule.mem_map_of_mem hvS, fun h => hv0 (hinj v hvS h), fun θ hθ => ?_⟩
    rw [← hf _ hθ, hvw θ hθ, map_smul]
  · rintro ν _ ⟨x, hx, rfl⟩ h0 hν
    exact hwt ν x hx (fun h => h0 (by rw [h, map_zero])) (hwt' x hx ν hν)

theorem exists_khw_genSub_of_kType (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    ∃ w : D, w ∈ genSub E V ∧ w ≠ 0 ∧ IsKHWVec ε E μ w := by
  classical
  have hE := hD.glRep
  obtain ⟨v, hvS, hv0, -⟩ := hST.2.2.2.1
  have hex : ∃ y : D, y ∈ genSub E V ∧ inner ℂ v (y : H) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h1 : (genSub E V).map D.subtype ≤ (ℂ ∙ v)ᗮ := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact hno y hy
    have h2 : closGen E V ≤ (ℂ ∙ v)ᗮ :=
      Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
    have h3 := h2 (hS hvS)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h3
    exact hv0 (inner_self_eq_zero.1 h3)
  obtain ⟨y, hyg, hyv⟩ := hex
  obtain ⟨m, hym⟩ := exists_layer_of_mem_genSub hE hVk hyg
  have hLf : FiniteDimensional ℂ (layer ε E V m) := finiteDimensional_layer hVf m
  have hLk := kStable_of_isKStableSub hσ hD (layer ε E V m) hLf (layer_kStable hE hVk m)
  set W : Submodule ℂ H := (layer ε E V m).map D.subtype with hWdef
  have : FiniteDimensional ℂ W := inferInstance
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hWK : ∀ k ∈ Kset ε, ∀ x ∈ W, σ k x ∈ W := by
    rintro k hk _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw, e⟩ := hLk k hk u hu
    exact ⟨w, hw, e⟩
  have hWoK : ∀ k ∈ Kset ε, ∀ x ∈ Wᗮ, σ k x ∈ Wᗮ := by
    intro k hk
    obtain ⟨hk', hkk⟩ := UnitaryGroupOfForm.K_inv hk
    exact UnitaryGroupOfForm.orth_stable hσ (UnitaryGroupOfForm.K_mem_UJ hk) (UnitaryGroupOfForm.K_mem_UJ hk') hkk W (hWK _ hk')
  have hPc : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, W.starProjection.toLinearMap (σ k x) =
      σ k (W.starProjection.toLinearMap x) := fun k hk x =>
    UnitaryGroupOfForm.proj_comm W (σ k) (hWK k hk) (hWoK k hk) x
  have hyW : (y : H) ∈ W := ⟨y, hym, rfl⟩
  have hinj : ∀ x ∈ S, W.starProjection.toLinearMap x = 0 → x = 0 := by
    intro x hx hPx
    let T : Submodule ℂ H := S ⊓ LinearMap.ker W.starProjection.toLinearMap
    have hT : Formalism.MainNotions.S.IsKStableOn ε σ T := fun g hg z hz =>
      ⟨hST.2.1 g hg z hz.1, LinearMap.mem_ker.2 (by rw [hPc g hg, LinearMap.mem_ker.1 hz.2, map_zero])⟩
    rcases hST.2.2.1 T inf_le_left hT with h | h
    · have hxT : x ∈ T := ⟨hx, hPx⟩
      rw [h, Submodule.mem_bot] at hxT
      exact hxT
    · exfalso
      have hvT : v ∈ T := by rw [h]; exact hvS
      apply hyv
      have e1 : inner ℂ v (y : H) = inner ℂ (W.starProjection v) (y : H) := by
        rw [Submodule.inner_starProjection_left_eq_right, W.starProjection_eq_self_iff.2 hyW]
      rw [e1, show W.starProjection v = 0 from hvT.2, inner_zero_left]
  have hKT := kType_map_of_inj hST W.starProjection.toLinearMap hPc hinj
  have hSD : S.map W.starProjection.toLinearMap ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨u, -, e⟩ := W.starProjection_apply_mem x
    show W.starProjection x ∈ D
    rw [← e]
    exact u.2
  obtain ⟨w, hwS, hw0, hwK⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hKT hSD
  refine ⟨w, ?_, hw0, hwK⟩
  obtain ⟨x, -, e⟩ := hwS
  obtain ⟨u, hu, e'⟩ := W.starProjection_apply_mem x
  have huw : u = w := Subtype.ext (e'.trans e)
  exact layer_le_genSub m (huw ▸ hu)

theorem data_casValK_gap (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {μ : Fin n → ℝ} (S : Submodule ℂ H)
    (hS : S ≤ closGen E V) (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) (hμ : μ ≠ lowK ε lam) :
    casValK ε (lowK ε lam) + 2 * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  obtain ⟨j, -, hpos, hle⟩ := casimir_gap_at_noncompact_weight hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap.1 hh hbig
    hwg hw0 hwK hμ
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith

theorem data_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {μ : Fin n → ℝ} (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ μ S) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ := by
  obtain ⟨w, hwg, hw0, hwK⟩ := exists_khw_genSub_of_kType hσ hD hV.1 hV.2.1 hS hST
  exact vogan_min hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwg hw0 hwK

theorem data_isKTypeOf (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) (V.map D.subtype) := by
  exact isKTypeOf_of_isKIrrHW hσ hD hV hVK (fun μ x hx hx0 hμ =>
    weights_le_of_irr_hw hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hx hx0 hμ)

theorem data_casU (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (x : D) (hx : x ∈ genSub E V) :
    casU ε σ (x : H) = ((casVal lam : ℝ) : ℂ) • (x : H) := by
  rw [casU_eq_casimir hD x, casimir_genSub hD.glRep hc x hx, Submodule.coe_smul]

theorem data_closGen_eq_top (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) (hV0 : V ≠ ⊥) :
    closGen E V = ⊤ := by
  rcases hirr (closGen E V) (Submodule.isClosed_topologicalClosure _)
      (closGen_stable hgap hσ hD hV hc hVK) with h | h
  · exfalso
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    have hwc : (w : H) ∈ closGen E V := UnitaryGroupOfForm.mem_closGen (E := E) V w hw
    rw [h, Submodule.mem_bot] at hwc
    exact hw0 (by exact_mod_cast hwc)
  · exact h

end Data

section Two

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {D₁ : Submodule ℂ H₁}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {V₁ : Submodule ℂ D₁}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂}
  {E₂ : Fin n → Fin n → Module.End ℂ D₂} {V₂ : Submodule ℂ D₂}

end Two

end ReciprocityTheory.ChartRestriction.DS
end
end
