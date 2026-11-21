import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mem_roots_iff_spec {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : K) :
    z ∈ M.charpoly.roots ↔ z ∈ spectrum K M := by
  rw [mem_roots M.charpoly_monic.ne_zero, Matrix.mem_spectrum_iff_isRoot_charpoly]

private theorem roots_aeval {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (p : K[X]) (w : K)
    (hw : w ∈ (aeval M p).charpoly.roots) : ∃ z ∈ M.charpoly.roots, p.eval z = w := by
  rw [mem_roots_iff_spec] at hw
  have hnt : Nontrivial (Matrix (Fin n) (Fin n) K) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hw (isUnit_of_subsingleton _)
  rw [spectrum.map_polynomial_aeval_of_nonempty M p (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K M)] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, (mem_roots_iff_spec M z).2 hz, rfl⟩

private theorem sum_eq_count {K : Type} [Field K] [DecidableEq K] (c : K) (hc : c ≠ 0) (s : Multiset K)
    (h : ∀ w ∈ s, w = 0 ∨ w = c) : s.sum = (s.count c : K) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))]
    rcases h a (Multiset.mem_cons_self _ _) with rfl | rfl
    · rw [Multiset.count_cons_of_ne hc]; simp
    · rw [Multiset.count_cons_self]; push_cast; ring

theorem UpperTheory.V.Ws.Pu.cpAlg :
    ∀ {O K Γ S : Type} [CommRing O] [Field K] [CharZero K] [IsAlgClosed K] [Algebra O K] [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (t : Finset S) (d : S → ℕ) (σ : ∀ i, Γ →* GL (Fin (d i)) K),
      (∀ g, (W.mat ρ g).charpoly = ∏ i ∈ t, (W.mat (σ i) g).charpoly) → ∀ (y : MonoidAlgebra O Γ), ∀ i ∈ t,
        ∀ z ∈ (MonoidAlgebra.lift O (Matrix (Fin (d i)) (Fin (d i)) K) Γ (W.mat (σ i)) y).charpoly.roots,
          z ∈ (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) y).charpoly.roots := by
  intro O K Γ S _ _ _ _ _ _ n ρ t d σ hcp y i hi z hz
  classical
  have h1 : ∀ g, (W.mat ρ g).trace = ∑ j ∈ t, (W.mat (σ j) g).trace := by
    intro g
    simp only [Matrix.trace_eq_sum_roots_charpoly]
    rw [hcp g, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun j _ => (Matrix.charpoly_monic _).ne_zero), Multiset.sum_bind]
    rfl
  have h2 : ∀ x : MonoidAlgebra O Γ, (MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) x).trace =
      ∑ j ∈ t, (MonoidAlgebra.lift O (Matrix (Fin (d j)) (Fin (d j)) K) Γ (W.mat (σ j)) x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, Matrix.trace_add, ha, hb, Finset.sum_add_distrib]
    | single g a => simp only [MonoidAlgebra.lift_single, Matrix.trace_smul, h1, Finset.smul_sum]
  set M := MonoidAlgebra.lift O (Matrix (Fin n) (Fin n) K) Γ (W.mat ρ) y with hM
  set N := fun j => MonoidAlgebra.lift O (Matrix (Fin (d j)) (Fin (d j)) K) Γ (W.mat (σ j)) y with hN
  have h3 : ∀ p : K[X], (aeval M p).trace = ∑ j ∈ t, (aeval (N j) p).trace := by
    intro p
    induction p using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Matrix.trace_add, ha, hb, Finset.sum_add_distrib]
    | monomial k a =>
      have := h2 (y ^ k)
      simp only [map_pow] at this
      simp only [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, hM, hN, this, Finset.smul_sum]
  by_contra hzM
  let T : Finset K := (M.charpoly.roots.toFinset ∪ t.biUnion fun j => (N j).charpoly.roots.toFinset).erase z
  let p : K[X] := ∏ w ∈ T, (X - C w)
  have hpz : p.eval z ≠ 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.2 fun w hw => sub_ne_zero.2 (Finset.ne_of_mem_erase hw).symm
  have hpT : ∀ w ∈ T, p.eval w = 0 := by
    intro w hw
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero hw (sub_self _)
  have hM0 : (aeval M p).trace = 0 := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine Multiset.sum_eq_zero fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := roots_aeval M p w hw
    refine hpT u (Finset.mem_erase.2 ⟨?_, Finset.mem_union_left _ (Multiset.mem_toFinset.2 hu)⟩)
    rintro rfl
    exact hzM hu
  have hNj : ∀ j ∈ t, (aeval (N j) p).trace = ((aeval (N j) p).charpoly.roots.count (p.eval z) : K) * p.eval z := by
    intro j hj
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine sum_eq_count _ hpz _ fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := roots_aeval (N j) p w hw
    by_cases huz : u = z
    · exact Or.inr (by rw [huz])
    · exact Or.inl (hpT u (Finset.mem_erase.2 ⟨huz, Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, hj, Multiset.mem_toFinset.2 hu⟩)⟩))
  have h4 := h3 p
  rw [hM0, Finset.sum_congr rfl hNj, ← Finset.sum_mul, ← Nat.cast_sum] at h4
  have h5 := (mul_eq_zero.1 h4.symm).resolve_right hpz
  rw [Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at h5
  have h6 := h5 i hi
  rw [Multiset.count_eq_zero] at h6
  apply h6
  rw [mem_roots_iff_spec]
  exact spectrum.subset_polynomial_aeval (N i) p ⟨z, (mem_roots_iff_spec _ z).1 hz, rfl⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Pu.exists_separating_element {O A k : Type} [CommRing O] [Ring A] [Field k] [Algebra O A] [Algebra O k]
    {n : ℕ} (f g : Fin n → A →ₐ[O] k) (e : Fin n → Fin n → A)
    (h1 : ∀ a b, f a (e a b) = 1) (h0 : ∀ a b, g b (e a b) = 0) :
    ∃ y : A, (∀ a, f a y = 1) ∧ ∀ b, g b y = 0 := by
  let ya : Fin n → A := fun a => ((List.finRange n).map (e a)).prod
  have hf : ∀ a, f a (ya a) = 1 := by
    intro a
    simp only [ya, map_list_prod, List.map_map]
    apply List.prod_eq_one
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact h1 a b
  have hg : ∀ a b, g b (ya a) = 0 := by
    intro a b
    simp only [ya, map_list_prod, List.map_map]
    apply List.prod_eq_zero
    rw [List.mem_map]
    exact ⟨b, List.mem_finRange b, h0 a b⟩
  refine ⟨1 - ((List.finRange n).map (fun a => 1 - ya a)).prod, ?_, ?_⟩
  · intro a
    rw [map_sub, map_one, map_list_prod, List.map_map, List.prod_eq_zero, sub_zero]
    rw [List.mem_map]
    exact ⟨a, List.mem_finRange a, by simp [hf a]⟩
  · intro b
    rw [map_sub, map_one, map_list_prod, List.map_map, List.prod_eq_one, sub_self]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    simp [hg a b]

theorem UpperTheory.V.Ws.Pu.sepEl :
    ∀ {O Γ : Type} [CommRing O] [IsLocalRing O] [Group Γ] {n : ℕ} (χ ψ : Fin n → Γ →* (ResidueField O)ˣ), (∀ a b, χ a ≠ ψ b) →
      ∃ y : MonoidAlgebra O Γ, (∀ a, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a)) y = 1) ∧
        ∀ b, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b)) y = 0 := by
  intro O Γ _ _ _ n χ ψ hne
  have key : ∀ a b, ∃ e : MonoidAlgebra O Γ, MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a)) e = 1 ∧ MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b)) e = 0 := by
    intro a b
    obtain ⟨γ, hγ⟩ : ∃ γ, χ a γ ≠ ψ b γ := by
      by_contra hc
      push_neg at hc
      exact hne a b (MonoidHom.ext hc)
    have hu : ((χ a γ : ResidueField O) - (ψ b γ : ResidueField O)) ≠ 0 := sub_ne_zero.2 (fun h => hγ (Units.ext h))
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (ψ b γ : ResidueField O)
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective ((χ a γ : ResidueField O) - (ψ b γ : ResidueField O))⁻¹
    refine ⟨MonoidAlgebra.single γ s - MonoidAlgebra.single 1 (s * r), ?_, ?_⟩
    · simp only [map_sub, MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, map_one, Units.val_one, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, map_mul, hr, hs, mul_one]
      rw [← mul_sub, inv_mul_cancel₀ hu]
    · simp only [map_sub, MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, map_one, Units.val_one, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, map_mul, hr, hs, mul_one, sub_self]
  choose e he using key
  exact UpperTheory.V.Ws.Pu.exists_separating_element (fun a => MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (χ a))) (fun b => MonoidAlgebra.lift O (ResidueField O) Γ ((Units.coeHom _).comp (ψ b))) e (fun a b => (he a b).1) (fun a b => (he a b).2)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private noncomputable def twHom {O Γ : Type} [CommRing O] [Group Γ] (η : Γ →* Oˣ) : Γ →* MonoidAlgebra O Γ where
  toFun g := MonoidAlgebra.single g (η g : O)
  map_one' := by simp [MonoidAlgebra.one_def]
  map_mul' g h := by simp [MonoidAlgebra.single_mul_single]

private theorem lift_tw {O Γ A : Type} [CommRing O] [Group Γ] [Ring A] [Algebra O A] (η : Γ →* Oˣ) (f f' : Γ →* A)
    (h : ∀ g, f' g = (η g : O) • f g) (y : MonoidAlgebra O Γ) :
    MonoidAlgebra.lift O A Γ f (MonoidAlgebra.lift O (MonoidAlgebra O Γ) Γ (twHom η) y) = MonoidAlgebra.lift O A Γ f' y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single g a =>
    simp only [MonoidAlgebra.lift_single, h, map_smul, smul_smul]
    simp [twHom, MonoidAlgebra.lift_single, smul_smul]

private theorem mem_max {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : ‖(x : PadicAlgCl l)‖ < 1) : x ∈ maximalIdeal c.O := by
  haveI := c.fin
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, rfl⟩
  have hint : IsIntegral ℤ_[l] (((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) ((u⁻¹ : (c.O)ˣ) : c.O)).map c.O.val
  have h1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 hint
  have h2 : ((u : c.O) : PadicAlgCl l) * (((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h3 := congrArg norm h2
  rw [norm_mul, norm_one] at h3
  have h4 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : (c.O)ˣ) : c.O) : PadicAlgCl l)‖ < 1 :=
    calc _ ≤ ‖((u : c.O) : PadicAlgCl l)‖ * 1 := by gcongr
      _ < 1 := by simpa using hx
  linarith

private theorem pushCh_zpow_neg_zero_eq_mul_zpow_neg_one {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] (ε : Γ →* c.Oˣ) (g : Γ) :
    ((((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-((0 : ℕ) : ℤ))) g : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      algebraMap c.O (PadicAlgCl l) (ε g) *
        ((((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-((1 : ℕ) : ℤ))) g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
  have h := Units.mul_inv (Units.map (algebraMap c.O (PadicAlgCl l) : c.O →* PadicAlgCl l) (ε g))
  simp only [Nat.cast_zero, neg_zero, zpow_zero, MonoidHom.one_apply, Units.val_one, Nat.cast_one,
    zpow_neg, zpow_one, MonoidHom.inv_apply, W.pushCh, MonoidHom.comp_apply]
  rw [← h]
  rfl

theorem UpperTheory.V.Ws.Pu.mOne :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ : Type} [Group Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) (PadicAlgCl l)) (χ : Fin n → Γ →* (ResidueField c.O)ˣ) (ε : Γ →* c.Oˣ) (ε' : Γ →* (PadicAlgCl l)ˣ),
      RedTo c ρ χ → ε' = W.pushCh (algebraMap c.O (PadicAlgCl l)) ε → (∀ i j, χ i ≠ χ j * W.pushCh (residue c.O) ε) →
      ∀ (a : ℕ) (d m : Fin a → ℕ) (ρ' : ∀ i, Γ →* GL (Fin (d i)) (PadicAlgCl l)), (∀ i, 1 ≤ d i ∧ 1 ≤ m i) →
        (∀ g, (W.mat ρ g).charpoly = ∏ i, ∏ j ∈ Finset.range (m i), (W.mat (Af.tw (ρ' i) (ε' ^ (-(j : ℤ)))) g).charpoly) → ∀ i, m i = 1 := by
  intro l _ c Γ _ n ρ χ ε ε' hR hε hne a d m ρ' hdm hcp i
  subst hε
  by_contra hmi
  have h2 : 2 ≤ m i := by have := (hdm i).2; omega
  obtain ⟨y, hy1, hy0⟩ := Pu.sepEl (O := c.O) χ (fun b => χ b * W.pushCh (residue c.O) ε) (fun a b => hne a b)
  let Y := MonoidAlgebra.lift c.O (MonoidAlgebra c.O Γ) Γ (twHom ε) y
  let t : Finset (Σ _ : Fin a, ℕ) := Finset.univ.sigma (fun k => Finset.range (m k))
  let dd : (Σ _ : Fin a, ℕ) → ℕ := fun p => d p.1
  let σ : (p : Σ _ : Fin a, ℕ) → Γ →* GL (Fin (dd p)) (PadicAlgCl l) :=
    fun p => Af.tw (ρ' p.1) ((W.pushCh (algebraMap c.O (PadicAlgCl l)) ε) ^ (-(p.2 : ℤ)))
  have hcp' : ∀ g, (W.mat ρ g).charpoly = ∏ p ∈ t, (W.mat (σ p) g).charpoly := by
    intro g
    rw [hcp g, Finset.prod_sigma]
  have hroot : ∀ (M : Matrix (Fin (d i)) (Fin (d i)) (PadicAlgCl l)), ∃ z, z ∈ M.charpoly.roots := by
    intro M
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root M.charpoly (by
      rw [Polynomial.degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim]
      have := (hdm i).1
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
      omega)
    exact ⟨z, (Polynomial.mem_roots M.charpoly_monic.ne_zero).2 hz⟩
  obtain ⟨z, hz⟩ := hroot (MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 0⟩)) y)
  have hM : MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 1⟩)) Y =
      MonoidAlgebra.lift c.O _ Γ (W.mat (σ ⟨i, 0⟩)) y := by
    apply lift_tw
    intro g
    simp only [σ, W.mat, MonoidHom.comp_apply, Units.coeHom_apply, Af.tw_val]
    rw [← IsScalarTower.algebraMap_smul (PadicAlgCl l) ((ε g : c.O)), smul_smul, ← pushCh_zpow_neg_zero_eq_mul_zpow_neg_one]
  have hz0 := Pu.cpAlg ρ t dd σ hcp' y ⟨i, 0⟩ (by simp [t]; omega) z hz
  have hz1 := Pu.cpAlg ρ t dd σ hcp' Y ⟨i, 1⟩ (by simp [t]; omega) z (by rw [hM]; exact hz)
  obtain ⟨j0, a0, ha0, hza0⟩ := hR y z hz0
  obtain ⟨j1, a1, ha1, hza1⟩ := hR Y z hz1
  rw [hy1] at ha0
  have hY0 : MonoidAlgebra.lift c.O (ResidueField c.O) Γ ((Units.coeHom (ResidueField c.O)).comp (χ j1)) Y = 0 := by
    rw [lift_tw ε _ ((Units.coeHom (ResidueField c.O)).comp (χ j1 * W.pushCh (residue c.O) ε)) _ y]
    · exact hy0 j1
    · intro g
      simp [Algebra.smul_def, W.pushCh, mul_comm]
  rw [hY0] at ha1
  have hm : a0 - a1 ∈ maximalIdeal c.O := mem_max c _ (by
    have e : ((a0 - a1 : c.O) : PadicAlgCl l) = (z - a1) + -(z - a0) := by push_cast; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [norm_neg]
    exact max_lt hza1 hza0)
  have hr : residue c.O (a0 - a1) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
  rw [map_sub, ha0, ha1, sub_zero] at hr
  exact one_ne_zero hr
end
