import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (J : Subgroup G), IsOpen (J : Set G) → μ (J : Set G) = 1 → ∀ S : Set G, IsCompact S → (∀ j ∈ J, ∀ g ∈ S, j * g ∈ S) → ∀ f : G → ℂ, (∀ j ∈ J, ∀ g, f (j * g) = f g) → ∀ M : AddSubgroup ℂ, (∀ g ∈ S, f g ∈ M) → ∫ g in S, f g ∂μ ∈ M := by
  intro G _ _ _ _ _ μ _ J hJ hμ S hS hSJ f hf M hM
  classical
  let C : G → Set G := fun a => (fun x => x * a⁻¹) ⁻¹' (J : Set G)
  have hCo : ∀ a, IsOpen (C a) := fun a => hJ.preimage (continuous_id.mul continuous_const)
  have hCμ : ∀ a, μ (C a) = 1 := fun a => by
    simp only [C]; rw [measure_preimage_mul_right, hμ]
  have hCf : ∀ a, Set.EqOn f (fun _ => f a) (C a) := fun a x hx => by
    have := hf (x * a⁻¹) hx a
    rw [inv_mul_cancel_right] at this
    exact this
  have hCi : ∀ a, IntegrableOn f (C a) μ := fun a => by
    refine IntegrableOn.congr_fun ?_ (hCf a).symm (hCo a).measurableSet
    exact integrableOn_const (by rw [hCμ]; simp)
  have hCint : ∀ a, ∫ g in C a, f g ∂μ = f a := fun a => by
    rw [setIntegral_congr_fun (hCo a).measurableSet (hCf a), setIntegral_const]
    simp [Measure.real, hCμ]
  have key : ∀ t : Finset G, (∀ g ∈ t, f g ∈ M) →
      IntegrableOn f (⋃ g ∈ t, C g) μ ∧ ∫ g in ⋃ g ∈ t, C g, f g ∂μ ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun g hg => h g (Finset.mem_insert_of_mem hg)
      rw [Finset.set_biUnion_insert]
      refine ⟨(hCi a).union h1, ?_⟩
      by_cases hd : Disjoint (C a) (⋃ g ∈ t, C g)
      · rw [setIntegral_union hd
          (isOpen_biUnion fun g _ => hCo g).measurableSet (hCi a) h1, hCint]
        exact M.add_mem (h a (Finset.mem_insert_self _ _)) h2
      · rw [Set.not_disjoint_iff] at hd
        obtain ⟨x, hx1, hx2⟩ := hd
        simp only [Set.mem_iUnion] at hx2
        obtain ⟨b, hb, hxb⟩ := hx2
        have hsub : C a ⊆ ⋃ g ∈ t, C g := by
          intro y hy
          simp only [Set.mem_iUnion]
          refine ⟨b, hb, ?_⟩
          have := J.mul_mem (J.mul_mem hy (J.inv_mem hx1)) hxb
          show y * b⁻¹ ∈ (J : Set G)
          simpa [mul_assoc] using this
        rw [Set.union_eq_self_of_subset_left hsub]
        exact h2
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover C (fun x _ => (hCo x).mem_nhds (by
    show x * x⁻¹ ∈ (J : Set G)
    simp))
  have hEq : S = ⋃ g ∈ t, C g := by
    refine Set.Subset.antisymm hcov ?_
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    have := hSJ _ hyb b (ht b hb)
    simpa using this
  rw [hEq]
  exact (key t fun g hg => hM g (ht g hg)).2
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isCompact_scaledInt (ϖ : kˣ) (n : ℕ) (m : ℤ) :
    IsCompact (GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) := by
  have h := (isCompact_intMatrix (k := k) (m := Fin n) (n := Fin n)).image
    (f := fun A : Matrix (Fin n) (Fin n) k => ((ϖ ^ m : kˣ) : k) • A) (by fun_prop)
  convert h using 1
  have h0 : valuation k ((ϖ ^ m : kˣ) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  ext Z
  constructor
  · intro hZ
    refine ⟨(((ϖ ^ m)⁻¹ : kˣ) : k) • Z, fun i j => ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hZ i j) zero_le
    · simp only [smul_smul, Units.mul_inv, one_smul]
  · rintro ⟨A, hA, rfl⟩ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))

private theorem mem_SB_of_periodic (ϖ : kˣ) {n : ℕ} (m : ℤ) (φ : Matrix (Fin n) (Fin n) k → ℂ)
    (hS : Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) (hP : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ) :
    φ ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun X => ?_,
    HasCompactSupport.intro (isCompact_scaledInt ϖ n m) fun x hx => ?_⟩
  · have hn : (fun Y => Y - X) ⁻¹' {A : Matrix (Fin n) (Fin n) k | ∀ i j, A i j ∈ 𝒪[k]} ∈ nhds X :=
      (isOpen_intMatrix.preimage (continuous_id.sub continuous_const)).mem_nhds (by
        intro i j; simp)
    filter_upwards [hn] with Y hY
    have := hP X (Y - X) (fun i j => by
      simpa using (Valuation.mem_integer_iff _ _).1 (hY i j))
    simpa using this
  · by_contra h
    exact hx (hS h)

private theorem isCompact_shellSet' (ϖ : kˣ) {n : ℕ} (m : Fin n → ℤ) :
    IsCompact (shellSet ϖ m : Set (GL (Fin n) k)) := by
  have h := ((isCompact_KO (k := k) (n := Fin n)).prod (isCompact_KO (k := k) (n := Fin n))).image
    (f := fun p : GL (Fin n) k × GL (Fin n) k => p.1 * (diagGL fun i => ϖ ^ m i) * p.2) (by fun_prop)
  convert h using 1
  ext g
  rw [mem_shellSet]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

end SlopeTestRemainingChoices

theorem UpperTheory.integral_mem_addSubgroup_of_ramified_twisted_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ} (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (J : Subgroup (GL (Fin n) k)), IsOpen (J : Set (GL (Fin n) k)) → J ≤ KO k (Fin n) → μ (J : Set (GL (Fin n) k)) = 1 → ∀ (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), IsUnif ϖ → ¬ IsUnram ν → CondLE ϖ e ν → ∀ (z : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (a : ℕ), Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n (-(a : ℤ)) → GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ → (∀ j ∈ J, ∀ g : GL (Fin n) k, φ (j.val * g.val) * (ν (gdet j) : ℂ) = φ g.val) → ∀ M : AddSubgroup ℂ, (∀ m : Fin n → ℤ, (∀ i, -(a : ℤ) ≤ m i ∧ m i < 0) → ∀ g ∈ shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∈ M) → ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ ∈ M := by
  intro k _ _ _ _ _ _ n μ _ J hJo hJK hJμ ϖ ν e hϖ hram hcond z φ a hS hP hinv M hM
  by_cases hint : Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) μ
  swap
  · rw [integral_undef hint]; exact M.zero_mem
  have hφ := mem_SB_of_periodic ϖ _ φ hS hP
  obtain ⟨-, h2, h3, h4⟩ := GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified k ϖ hϖ ν e hram hcond n μ φ hφ
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_haar μ
  have hsh : ∀ m : Fin n → ℤ, shell μ ϖ ν z φ m ∈ M := by
    intro m
    by_cases hm : ∀ i, -(a : ℤ) ≤ m i ∧ m i < 0
    · refine UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant μ J hJo hJμ (shellSet ϖ m) (isCompact_shellSet' ϖ m) ?_
        (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) ?_ M (hM m hm)
      · intro j hj g hg
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
        exact mem_shellSet.2 ⟨j * x, mul_mem (hJK hj) hx, y, hy, by simp only [mul_assoc]⟩
      · intro j hj g
        simp only [gdet_mul, apow_mul, map_mul, Units.val_mul,
          apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (hJK hj)), one_mul]
        rw [← hinv j hj g]
        ring
    · by_cases hm' : ∀ i, -(a : ℤ) ≤ m i
      · have : ∃ i, (0 : ℤ) ≤ m i := by
          by_contra h
          push_neg at h
          exact hm fun i => ⟨hm' i, h i⟩
        rw [h2 0 hP m this z]; exact M.zero_mem
      · rw [h3 a hS m hm' z]; exact M.zero_mem
  set S : {m : Fin n → ℤ // Antitone m} → Set (GL (Fin n) k) := fun m => shellSet ϖ m.1 with hSdef
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).unique h1 h2)
  have hm : ∀ m, MeasurableSet (S m) := fun m => (GlobalTheory.ShellSumEqv.isOpen_shellSet ϖ m.1).measurableSet
  have hfin : (Function.support fun m : {m : Fin n → ℤ // Antitone m} => shell μ ϖ ν z φ m.1).Finite :=
    h4.subset fun m hm => ⟨z, hm⟩
  have key : ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ =
      ∑ m ∈ hfin.toFinset, shell μ ϖ ν z φ m.1 :=
    calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ :=
          integral_iUnion hm hd hint.integrableOn
      _ = ∑ᶠ m : {m : Fin n → ℤ // Antitone m}, shell μ ϖ ν z φ m.1 := tsum_eq_finsum hfin
      _ = _ := finsum_eq_sum _ hfin
  rw [key]
  exact sum_mem fun m _ => hsh m.1
end
