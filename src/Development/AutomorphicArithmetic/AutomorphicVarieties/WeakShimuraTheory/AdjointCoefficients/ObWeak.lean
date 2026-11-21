import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MapAdjAlg

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_mat {S Q : Type} [TopologicalSpace S] {f : S → M4 Q}
    (h : ∀ i j, IsLocallyConstant fun s => f s i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ᶠ t in nhds s, ∀ i j, f t i j = f s i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq s
  exact this.mono fun t ht => Matrix.ext ht

private def corr {A : Type} [CommRing A] (c n : A) (y : M4 A) : M4 A := y * (1 - c • (adj y * y - n • 1))

private theorem corr_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c n : A) (y : M4 A) :
    (corr c n y).map f = corr (f c) (f n) (y.map f) := by
  obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
  rw [corr, corr, hm, ← Matrix.map_mul, Matrix.map_mul]
  generalize adj y * y = w
  congr 1
  ext i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem corr_gsp {A : Type} [CommRing A] (c n : A) (y : M4 A) (hc : 2 * c * n = 1)
    (hE : (adj y * y - n • 1) * (adj y * y - n • 1) = 0) : IsGSp n (corr c n y) := by
  obtain ⟨hmul, hadj, hadd, hsm, h1, -⟩ := grp A
  unfold IsGSp corr
  obtain ⟨E, hE'⟩ : ∃ E, E = adj y * y - n • 1 := ⟨_, rfl⟩
  have a1 : adj E = E := by
    rw [hE', sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, hmul, hadj]
  have a2 : adj y * y = E + n • 1 := by rw [hE', sub_add_cancel]
  rw [← hE'] at hE ⊢
  have a3 : adj (1 - c • E) = 1 - c • E := by
    rw [sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, a1]
  rw [hmul, a3, mul_assoc, ← mul_assoc (adj y), a2]
  simp only [mul_sub, sub_mul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, hE, one_mul, mul_one, smul_zero,
    smul_add, smul_sub, smul_smul, zero_add, sub_zero]
  have : E = (2 * c * n) • E := by rw [hc, one_smul]
  linear_combination (norm := module) this

private theorem up_mul {A : Type} [CommRing A] {X Y : M4 A} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k < i
  · rw [hX i k e, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 e)), mul_zero]

private theorem corr_up {A : Type} [CommRing A] (c n : A) {y : M4 A} (hy : IsUp y) : IsUp (corr c n y) := by
  have a : IsUp (adj y) := fun i j h => by
    rw [adj_apply, hy _ _ (Fin.rev_lt_rev.2 h), smul_zero]
  refine up_mul hy fun i j h => ?_
  simp [up_mul a hy i j h, Matrix.one_apply_ne h.ne']

theorem UpperTheory.V.Ws.X1.gspLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (S : Type) [TopologicalSpace S] (ν : S → Λˣ) (x : S → M4 R), AdicCont (maximalIdeal Λ) (fun s => (ν s : Λ)) → (∀ i j, AdicCont (maximalIdeal R) fun s => x s i j) → (∀ s, IsGSp (algebraMap Λ R (ν s)) (x s)) → ∃ y : S → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧ (∀ s, IsGSp (algebraMap Λ A (ν s)) (y s)) ∧ (∀ s, (y s).map p = x s) ∧ ((∀ s, IsUp (x s)) → ∀ s, IsUp (y s)) := by
  intro Λ _ _ _ _ h2 A R _ _ _ _ _ _ p hp hs S _ ν x hν hx hg
  classical
  choose z z1 z2 using fun i j => (UpperTheory.V.Ws.X1.contLift p hp hs).1 S (fun s => x s i j) (hx i j)
  let y0 : S → M4 A := fun s => Matrix.of fun i j => if ∀ t, x t i j = 0 then 0 else z i j s
  have b0 : ∀ i j, AdicCont (maximalIdeal A) fun s => y0 s i j := fun i j => by
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.of_apply, if_pos e]
      exact fun _ => IsLocallyConstant.const _
    · simp only [y0, Matrix.of_apply, if_neg e]
      exact z1 i j
  have b1 : ∀ s, (y0 s).map p = x s := fun s => by
    ext i j
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_pos e, map_zero, e s]
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_neg e, z2]
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  have hk : ∀ a b : A, p a = 0 → p b = 0 → a * b = 0 := fun a b ha hb => by
    have ha' : a ∈ maximalIdeal A := fun h => by
      have := h.map p
      rw [ha] at this
      exact not_isUnit_zero this
    have : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul ha' hb
    rwa [hs, Ideal.mem_bot] at this
  have hE : ∀ s i j, p ((adj (y0 s) * y0 s - algebraMap Λ A (ν s) • (1 : M4 A)) i j) = 0 := fun s i j => by
    obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
    have e1 : (adj (y0 s) * y0 s).map p = algebraMap Λ R (ν s) • (1 : M4 R) := by
      have := hm R (p : A →+* R) (y0 s)
      simp only [RingHom.coe_coe] at this
      rw [Matrix.map_mul, ← this, b1]
      exact hg s
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.sub_apply, map_sub, e2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  refine ⟨fun s => corr (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s), fun i j N => ?_,
    fun s => corr_gsp _ _ _ ?_ ?_, fun s => ?_, fun h s => corr_up _ _ fun i j e => ?_⟩
  · let q := Ideal.Quotient.mk (maximalIdeal A ^ N)
    have c1 : IsLocallyConstant fun s => (y0 s).map q := lc_mat fun i j => b0 i j N
    have c2 : IsLocallyConstant fun s => q (algebraMap Λ A (ν s)) := by
      have hle : maximalIdeal Λ ^ N ≤ (maximalIdeal A ^ N).comap (algebraMap Λ A) :=
        (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.1 (map_maximalIdeal_le (algebraMap Λ A))) N).trans
          (Ideal.le_comap_pow _ N)
      exact (hν N).comp (Ideal.quotientMap _ _ hle)
    have c3 : ∀ s, q (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) =
        q (algebraMap Λ A u) * Ring.inverse (q (algebraMap Λ A (ν s))) := fun s => by
      rw [map_mul, map_mul]
      congr 1
      exact (Ring.inverse_unit (Units.map (q.comp (algebraMap Λ A)).toMonoidHom (ν s))).symm
    have c4 := (c1.prodMk c2).comp fun w => corr (q (algebraMap Λ A u) * Ring.inverse w.2) w.2 w.1 i j
    convert c4 using 2 with s
    simp only [Function.comp_apply]
    rw [← c3, ← corr_map]
    rfl
  · rw [← map_ofNat (algebraMap Λ A) 2, ← map_mul, ← map_mul, ← mul_assoc, hu, one_mul, Units.inv_mul, map_one]
  · ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hk _ _ (hE s i k) (hE s k j)
  · have := corr_map (p : A →+* R) (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s)
    simp only [RingHom.coe_coe] at this
    have g := hg s
    unfold IsGSp at g
    rw [this, b1, corr, g, p.commutes (ν s), sub_self, smul_zero, sub_zero, mul_one]
  · simp only [y0, Matrix.of_apply, if_pos fun t => h t i j e]
end

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isLocallyConstant_finset_sum {S Y ι : Type} [TopologicalSpace S] [AddCommMonoid Y] (t : Finset ι)
    (f : ι → S → Y) (h : ∀ i ∈ t, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ t, f i x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : Y)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsLocallyConstant.comp₂ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (· + ·)

private theorem cont_conj {S R : Type} [TopologicalSpace S] [CommRing R] (I : Ideal R) (x : S → M4 R) (a b : M4 R)
    (h : ∀ i j, AdicCont I fun s => x s i j) (i j : Fin 4) : AdicCont I fun s => (a * x s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j)) = fun s =>
      ∑ l, (∑ k, Ideal.Quotient.mk (I ^ N) (a i k) * Ideal.Quotient.mk (I ^ N) (x s k l)) *
        Ideal.Quotient.mk (I ^ N) (b l j) := by
    funext s
    simp [Matrix.mul_apply, map_sum, map_mul]
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j))
  rw [e]
  refine isLocallyConstant_finset_sum _ _ fun l _ => ?_
  refine IsLocallyConstant.comp₂ ?_ (IsLocallyConstant.const _) (· * ·)
  refine isLocallyConstant_finset_sum _ _ fun k _ => ?_
  exact IsLocallyConstant.comp₂ (IsLocallyConstant.const _) (h k l N) (· * ·)

private theorem cont_push {Λ S A A' : Type} [CommRing Λ] [IsLocalRing Λ] [TopologicalSpace S] [CommRing A] [Algebra Λ A]
    [IsCO Λ A] [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p : A →ₐ[Λ] A') (x : S → A)
    (h : AdicCont (maximalIdeal A) x) : AdicCont (maximalIdeal A') fun s => p (x s) := by
  intro N
  have hm : Ideal.map p (maximalIdeal A) ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff Λ A', res_map, res_eq_zero_iff]
    exact hy
  have hle : maximalIdeal A ^ N ≤ Ideal.comap p (maximalIdeal A' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' hm N
  have e : (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s))) =
      fun s => Ideal.quotientMap (maximalIdeal A' ^ N) (p : A →+* A') hle (Ideal.Quotient.mk (maximalIdeal A ^ N) (x s)) := by
    funext s
    rfl
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s)))
  rw [e]
  exact (h N).comp _

private theorem gsp_conj {R : Type} [CommRing R] {c : R} {x n : M4 R} (hx : IsGSp c x) (hn : IsGSp 1 n) :
    IsGSp c (adj n * x * n) := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have hn1 : adj n * n = 1 := by
    have := hn
    unfold IsGSp at this
    rw [this, one_smul]
  have hn2 : n * adj n = 1 := mul_eq_one_comm.mp hn1
  have hx' : adj x * x = c • 1 := hx
  show adj (adj n * x * n) * (adj n * x * n) = c • 1
  rw [hmul, hmul, hadj]
  calc adj n * (adj x * n) * (adj n * x * n) = adj n * (adj x * (n * adj n) * x) * n := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [hn2, Matrix.mul_one, hx', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hn1]

private theorem gsp_push {Λ A A' : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing A'] [Algebra Λ A']
    (p : A →ₐ[Λ] A') {c : Λ} {x : M4 A} (hx : IsGSp (algebraMap Λ A c) x) : IsGSp (algebraMap Λ A' c) (x.map p) := by
  have := isGSp_map (p : A →+* A') hx
  rwa [AlgHom.coe_toRingHom, AlgHom.commutes] at this

theorem UpperTheory.V.Ws.X1.slEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∃ D : SL loc ν r n p, ∀ (A' : Type) [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p' : A →ₐ[Λ] A') (p'' : A' →ₐ[Λ] R), p''.comp p' = p → ∃ D' : SL loc ν r n p'', (∀ s t, D'.om s t = (D.om s t).map p') ∧ ∀ v s, D'.de v s = (D.de v s).map p' := by
  intro Λ _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hker ν r n hν hW hr
  obtain ⟨yr, hyc, hym, hyp, -⟩ := X1.gspLift h2 p hp hker Γ (fun g => ν g) (fun g => r g) hν hr hW.mult
  letI : TopologicalSpace V := ⊥
  haveI : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨yn, -, hnm, hnp, -⟩ := X1.gspLift h2 p hp hker V (fun _ => 1) n
    (by intro N; exact IsLocallyConstant.of_discrete _)
    (by intro i j N; exact IsLocallyConstant.of_discrete _)
    (fun v => by simpa using hW.sp v)
  have hnm' : ∀ v, IsGSp 1 (yn v) := fun v => by simpa using hnm v
  have ht : ∀ v, ∃ y : Gv v → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧
      (∀ s, IsGSp (algebraMap Λ A (ν (loc v s))) (y s)) ∧
      (∀ s, (y s).map p = adj (n v) * r (loc v s) * n v) ∧ ∀ s, IsUp (y s) := by
    intro v
    obtain ⟨y, h1, h2', h3, h4⟩ := X1.gspLift h2 p hp hker (Gv v) (fun s => ν (loc v s))
      (fun s => adj (n v) * r (loc v s) * n v)
      (by intro N; exact (hν N).comp_continuous (hloc v))
      (by
        intro i j
        exact cont_conj _ _ _ _ (fun i j N => (hr i j N).comp_continuous (hloc v)) i j)
      (fun s => gsp_conj (hW.mult _) (hW.sp v))
    exact ⟨y, h1, h2', h3, h4 (hW.flag v)⟩
  choose yt hyt using ht
  let D : SL loc ν r n p := ⟨yr, hyc, hym, hyp, yn, hnm', hnp, yt, fun v => (hyt v).1, fun v => (hyt v).2.1,
    fun v => (hyt v).2.2.2, fun v => (hyt v).2.2.1⟩
  refine ⟨D, ?_⟩
  intro A' _ _ _ p' p'' hpp
  have hc : ∀ a, p'' (p' a) = p a := fun a => by rw [← hpp]; rfl
  have hmap : ∀ X : M4 A, (X.map p').map p'' = X.map p := fun X => by
    ext i j
    simp [hc]
  have hm1 : ∀ X Y : M4 A, (X * Y).map p' = X.map p' * Y.map p' := fun X Y => by
    ext i j
    simp [Matrix.mul_apply, map_sum]
  have hm2 : ∀ X Y : M4 A, (X - Y).map p' = X.map p' - Y.map p' := fun X Y => by
    ext i j
    simp
  have hadj : ∀ X : M4 A, adj (X.map p') = (adj X).map p' := fun X => adj_map (p' : A →+* A') X
  refine ⟨⟨fun g => (yr g).map p', ?_, ?_, ?_, fun v => (yn v).map p', ?_, ?_, fun v s => (yt v s).map p',
    ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    exact cont_push p' _ (hyc i j)
  · intro g
    exact gsp_push p' (hym g)
  · intro g
    rw [hmap, hyp]
  · intro v
    have := isGSp_map (p' : A →+* A') (hnm' v)
    simpa using this
  · intro v
    rw [hmap, hnp]
  · intro v i j
    exact cont_push p' _ ((hyt v).1 i j)
  · intro v s
    exact gsp_push p' ((hyt v).2.1 s)
  · intro v s i j hij
    simp [(hyt v).2.2.2 s i j hij]
  · intro v s
    rw [hmap]
    exact (hyt v).2.2.1 s
  · intro s t
    show (yr s).map p' * (yr t).map p' - (yr (s * t)).map p' = (yr s * yr t - yr (s * t)).map p'
    rw [hm2, hm1]
  · intro v s
    show (yr (loc v s)).map p' - (yn v).map p' * (yt v s).map p' * adj ((yn v).map p') =
      (yr (loc v s) - yn v * yt v s * adj (yn v)).map p'
    rw [hm2, hm1, hm1, hadj]
end

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.coefEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {A : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (κ : Type) [Fintype κ] (ε : κ → A), K = Ideal.span (Set.range ε) → (∀ c : κ → Λ, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal Λ) → ∃ co : κ → A → ResidueField Λ, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res Λ A a * co u x) ∧ ∀ x ∈ K, ∃ a : κ → Λ, (∀ u, residue Λ (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro Λ _ _ A _ _ _ K hK κ _ ε hspan hind
  classical
  have hkill : ∀ m ∈ maximalIdeal A, ∀ e ∈ K, m * e = 0 := by
    intro m hm e he
    have h := Ideal.mul_mem_mul hm he
    rw [hK] at h
    exact (Submodule.mem_bot A).mp h
  have hsc : ∀ b : A, ∃ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A := fun b => IsCO.res_surj (O := Λ) b
  have hact : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → ∀ e ∈ K, b * e = l • e := by
    intro b l hb e he
    have h := hkill _ hb e he
    rw [sub_mul] at h
    rw [Algebra.smul_def]
    exact sub_eq_zero.mp h
  have hres : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → res Λ A b = residue Λ l := by
    intro b l hb
    have h := (res_eq_zero_iff Λ A _).mpr hb
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h
    rw [h]
    rfl
  have hex : ∀ x ∈ K, ∃ a : κ → Λ, x = ∑ u, a u • ε u := by
    intro x hx
    have hx' := hx
    rw [hspan] at hx'
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    choose l hl using fun u => hsc (b u)
    refine ⟨l, ?_⟩
    rw [← hb]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]
    refine hact _ _ (hl u) _ ?_
    rw [hspan]
    exact Ideal.subset_span ⟨u, rfl⟩
  have huniq : ∀ a a' : κ → Λ, ∑ u, a u • ε u = ∑ u, a' u • ε u →
      ∀ u, residue Λ (a u) = residue Λ (a' u) := by
    intro a a' h u
    have h0 := hind (a - a') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]) u
    rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h0
  let co : κ → A → ResidueField Λ := fun u x => if h : x ∈ K then residue Λ ((hex x h).choose u) else 0
  have hco : ∀ x (h : x ∈ K) (a : κ → Λ), x = ∑ u, a u • ε u → ∀ u, co u x = residue Λ (a u) := by
    intro x h a hx u
    simp only [co, dif_pos h]
    exact huniq _ _ ((hex x h).choose_spec.symm.trans hx) u
  refine ⟨co, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨b, hb⟩ := hex y hy
    rw [hco x hx a ha, hco y hy b hb, hco (x + y) (K.add_mem hx hy) (a + b)
      (by rw [ha, hb, ← Finset.sum_add_distrib]; simp [add_smul]), Pi.add_apply, map_add]
  · intro u c x hx
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨l, hl⟩ := hsc c
    rw [hco x hx a ha, hco (c * x) (K.mul_mem_left c hx) (l • a) ?_, hres c l hl, Pi.smul_apply, smul_eq_mul,
      map_mul]
    rw [hact c l hl x hx, ha, Finset.smul_sum]
    simp [smul_smul]
  · intro x hx
    obtain ⟨a, ha⟩ := hex x hx
    exact ⟨a, fun u => (hco x hx a ha u).symm, ha⟩
end

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exists_strictHenselian_absolutely_closed_local_ring {k A : Type} [CommRing k] [CommRing A] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : M4 k →+ M4 A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : M4 A) Y, M * T Y = T (M.map π * Y)) ∧
      (∀ (M : M4 A) Y, T Y * M = T (Y * M.map π)) ∧ (∀ Y, adj (T Y) = T (adj Y)) ∧
      ∀ Y, IsUp Y → IsUp (T Y) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_, fun Y => ?_, fun Y hY i j h => ?_⟩
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]
  · simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, hY i j h, map_zero]

private theorem isUp_mul {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hX i c hc, zero_mul]
  · rw [hY c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

private theorem isUp_add {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X + Y) := by
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

private theorem alg_id {S : Type} [Ring S] (a n B g y : S) (h : n * a = 1) :
    a * (B * g - (g * y - y * g)) * n + (a * (g * (y * n)) + a * -y * g * n) = a * B * n * (a * g * n) := by
  have : a * B * n * (a * g * n) = a * B * (n * a) * g * n := by simp only [mul_assoc]
  rw [this, h]
  noncomm_ring

private theorem rb_lc {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {Γ : Type} [TopologicalSpace Γ]
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (r : Γ → M4 R) (rb : Γ → M4 (ResidueField Λ))
    (hc : ∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) (hr : ∀ g, (r g).map (res Λ R) = rb g) :
    IsLocallyConstant rb := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rb t a b = rb s a b := fun a b => by
    filter_upwards [(hc a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff Λ, map_sub, sub_eq_zero] at ht
    rw [← hr, ← hr]
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

theorem UpperTheory.V.Ws.X1.obCor :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → ∀ (D : SL loc ν r n p) (μ : ResidueField Λ → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res Λ A a * c) = a * μ c) → (∀ c, p (μ c) = 0) → ∀ x ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)), (∀ s t, D.om s t = ((x.1 (s, t)).1 * rb (s * t)).map μ) → (∀ v s, D.de v s = ((x.2 v s).1 * rb (loc v s)).map μ) → WLift loc ν r n p := by
  intro Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n hν hW hc rb nb hb hr hn D μ m1 m2 m3
    x hx x1 x2
  obtain ⟨T, T0, Tl, Tr, Ta, Tu⟩ := exists_strictHenselian_absolutely_closed_local_ring (res Λ A) μ m1 m2
  simp only [T0, SL.om, SL.de] at x1 x2
  have lc := rb_lc r rb hc hr
  obtain ⟨h, y, b1, b3, b4⟩ := hx
  obtain ⟨class_group_mod_eq_torsion, -, gA3, -, -, gA6, -⟩ := grp A
  obtain ⟨gR1, -, -, -, -, gR6, -⟩ := grp R
  obtain ⟨gk1, -⟩ := grp (ResidueField Λ)
  have aA : ∀ X : M4 A, (adj X).map (res Λ A) = adj (X.map (res Λ A)) := fun X =>
    (gA6 _ (res Λ A : A →+* ResidueField Λ) X).symm
  have aR : ∀ X : M4 R, (adj X).map (res Λ R) = adj (X.map (res Λ R)) := fun X =>
    (gR6 _ (res Λ R : R →+* ResidueField Λ) X).symm
  have mR : ∀ X Y : M4 R, (X * Y).map (res Λ R) = X.map (res Λ R) * Y.map (res Λ R) := fun X Y =>
    Matrix.map_mul (f := (res Λ R : R →+* ResidueField Λ))
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res Λ A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res Λ A (μ _) = 0
    rw [← res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (D.rt s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hr, ← D.rt_map, Matrix.map_apply, Matrix.map_apply]
  have ntres : ∀ v, (D.nt v).map (res Λ A) = nb v := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hn, ← D.nt_map, Matrix.map_apply, Matrix.map_apply]
  have pert : ∀ (c : A) (g : M4 A) (Y : M4 (ResidueField Λ)), IsGSp c g → Y ∈ sp4 (ResidueField Λ) →
      IsGSp c (g + T (Y * g.map (res Λ A))) := fun c g Y hg hY => by
    have hY' : adj Y = -Y := hY
    unfold IsGSp at *
    rw [gA3, Ta, gk1, hY', add_mul, mul_add, mul_add, TT, Tl, Tr, hg, aA]
    simp only [mul_neg, neg_mul, map_neg, mul_assoc]
    abel
  have inv1 : ∀ s, rb s * rb s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rb s⁻¹ * rb s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → M4 A := fun s => D.rt s - T ((h s).1 * rb s) with hf
  have fH : ∀ s, IsGSp (algebraMap Λ A (ν s)) (f s) := fun s => by
    have := pert _ _ _ (D.rt_mult s) (-h s).2
    rw [rtres, Submodule.coe_neg, neg_mul, map_neg, ← sub_eq_add_neg] at this
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (adSp rb hb) h (s, t)).1 : M4 _) * rb (s * t) =
        (h s).1 * rb s * rb t + rb s * ((h t).1 * rb t) - (h (s * t)).1 * rb (s * t) := by
      show ((h s).1 + rb s * (h t).1 * rb s⁻¹ - (h (s * t)).1) * rb (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rb s * (h t).1), ← mul_assoc (rb s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add]
    abel
  have fone : f 1 = 1 := by
    have hu : adj (f 1) * f 1 = 1 := by
      have := fH 1
      unfold IsGSp at this
      rw [this]; simp
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = adj (f 1) * f 1 * f 1 := by rw [hu, one_mul]
      _ = 1 := by rw [mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, D.rt_map, sub_zero]
  have fres : ∀ s, (f s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hr, ← fp, Matrix.map_apply, Matrix.map_apply]
  refine ⟨{ toFun := f, map_one' := fone, map_mul' := fmul }, fun v => D.nt v + T ((y v).1 * nb v),
    ⟨fH, fun v => ?_, fun v s => ?_⟩, fun a b N => ?_, fp, fun v => ?_⟩
  · have := pert _ _ _ (D.nt_sp v) (y v).2
    rwa [ntres] at this
  · have n1 : adj (D.nt v) * D.nt v = 1 := by
      have := D.nt_sp v
      unfold IsGSp at this
      rw [this, one_smul]
    have n2 : adj (nb v) * nb v = 1 := by
      rw [← ntres, ← aA]
      have := congrArg (fun X : M4 A => X.map (res Λ A : A →+* ResidueField Λ)) n1
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have n3 : nb v * adj (nb v) = 1 := mul_eq_one_comm.1 n2
    have u1 : IsUp (adj (nb v) * rb (loc v s) * nb v) := fun i j hij => by
      rw [← hn, ← hr, ← aR, ← mR, ← mR, Matrix.map_apply, hW.flag v s i j hij, map_zero]
    have u2 : IsUp (adj (nb v) * ((x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)))
      * nb v) := b4 v s
    set B := (x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)) with hB
    have e := x2 v s
    rw [sub_eq_iff_eq_add] at e
    have hy : adj (y v).1 = -(y v).1 := (y v).2
    have e1 : f (loc v s) = D.nt v * D.t v s * adj (D.nt v) +
        T (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) := by
      have : B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)) =
          (x.2 v s).1 * rb (loc v s) - (h (loc v s)).1 * rb (loc v s) := by
        rw [hB, sub_mul, sub_mul, sub_mul, mul_assoc _ _ (rb (loc v s)), inv2, mul_one]
        abel
      rw [this, map_sub, hf]
      simp only
      rw [e]
      abel
    have e2 : adj (D.nt v) * f (loc v s) * D.nt v = D.t v s +
        T (adj (nb v) * (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) * nb v) := by
      rw [e1, mul_add, add_mul, Tl, Tr, aA, ntres]
      congr 1
      rw [← mul_assoc, ← mul_assoc, n1, one_mul, mul_assoc, n1, mul_one]
    have key : adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)) =
        D.t v s + T ((adj (nb v) * B * nb v) * (adj (nb v) * rb (loc v s) * nb v)) := by
      rw [gA3, Ta, gk1, hy, add_mul, add_mul, mul_add, mul_add, e2, Tr (f _), TT, Tr (D.nt v),
        mul_assoc (adj (D.nt v)), Tl, Tl, fres, aA, ntres, add_zero, add_assoc, add_assoc, ← map_add, ← map_add]
      exact congrArg (fun Z => D.t v s + T Z) (alg_id _ _ _ _ _ n3)
    show IsUp (adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)))
    rw [key]
    exact isUp_add (D.t_up v s) (Tu _ (isUp_mul u2 u1))
  · have c1 := D.rt_cont a b N
    have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rb s) a b) :=
      ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
    have c3 := c1.sub c2
    convert c3 using 2 with s
    exact map_sub _ _ _
  · show (D.nt v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero, D.nt_map]
end

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ex_mu {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A] (η : A)
    (hη : ∀ x ∈ maximalIdeal A, x * η = 0) :
    ∃ μ : ResidueField O →+ A, (∀ a : O, μ (residue O a) = a • η) ∧ ∀ (a : A) c, μ (res O A a * c) = a * μ c := by
  have k : ∀ a b : O, residue O a = residue O b → a • η = b • η := fun a b h => by
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    refine hη _ ?_
    rw [← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]
  choose s hs using residue_surjective (R := O)
  have k2 : ∀ a : O, s (residue O a) • η = a • η := fun a => k _ _ (hs _)
  refine ⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩
  · rw [← add_smul]
    exact k _ _ (by rw [map_add, hs, hs, hs])
  · obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
    have e : res O A a = residue O b := by
      have := (res_eq_zero_iff O A _).2 hb
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
    have e2 : a * η = b • η := by
      have := hη _ hb
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at this
    show s _ • η = a * (s c • η)
    rw [mul_smul_comm, e2, smul_smul]
    exact k _ _ (by rw [map_mul, hs, hs, e, mul_comm])

private theorem mmap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

private theorem smap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A - B).map f = A.map f - B.map f := by
  ext i j
  simp

private theorem amap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A : M4 R) : (adj A).map f = adj (A.map f) := by
  ext i j
  rw [Matrix.map_apply, adj_apply, adj_apply, map_zsmul, Matrix.map_apply]

theorem UpperTheory.V.Ws.X1.obWeak :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → Obs Λ R (Fr.coneH2 loc (adSp rb hb) fun v => bor (nb v)) fun A' _ _ _ q => Function.Surjective q ∧ maximalIdeal A' * RingHom.ker q = ⊥ ∧ WLift loc ν r n q := by
  intro O _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc R _ _ _ ν r n hν hw hr rb nb hb hrb hnb A _ _ _ p hp hs κ _ ε hK hind
  classical
  obtain ⟨D, hD⟩ := X1.slEx h2 loc hloc p hp hs ν r n hν hw hr
  obtain ⟨co, k1, k2, k4⟩ := X1.coefEx (RingHom.ker p) hs κ ε hK hind
  choose z z0 z1 z2 using fun u : κ =>
    X1.obCoc loc hloc p hp hs ν r n hν hw hr rb nb hb hrb hnb D (co u) (k1 u) (k2 u)
  have d1 : ∀ s t, (D.om s t).map p = 0 := fun s t => by
    rw [SL.om, smap, mmap, D.rt_map, D.rt_map, D.rt_map, map_mul, sub_self]
  have d2 : ∀ v s, (D.de v s).map p = 0 := fun v s => by
    have e1 : adj (n v) * n v = 1 := by
      have := hw.sp v
      rwa [IsGSp, one_smul] at this
    have e2 : n v * adj (n v) = 1 := mul_eq_one_comm.1 e1
    rw [SL.de, smap, mmap, mmap, amap, D.rt_map, D.nt_map, D.t_map, ← mul_assoc, ← mul_assoc, e2, one_mul,
      mul_assoc, e2, mul_one, sub_self]
  refine ⟨fun u => Submodule.Quotient.mk ⟨z u, z0 u⟩, ?_⟩
  intro c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1
  have hx : ∑ u, residue O (c u) • z u ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)) := by
    have h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) •
        (⟨z u, z0 u⟩ : Fr.continuousCocycles2 loc (adSp rb hb) (fun v => bor (nb v)))) :
        Fr.coneH2 loc (adSp rb hb) (fun v => bor (nb v))) = 0 := by
      rw [← hc, ← Submodule.mkQ_apply, map_sum]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum] at h1
    exact h1
  obtain ⟨μ, m1, m2⟩ := ex_mu (O := O) η hη
  have pp : ∀ x, p'' (p' x) = p x := fun x => DFunLike.congr_fun hpp x
  have key : ∀ x, p x = 0 → p' x = μ (∑ u, residue O (c u) * co u x) := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := k4 x hx
    have : ∑ u, residue O (c u) * co u x = residue O (∑ u, a u * c u) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]
    rw [this, m1, Finset.sum_smul]
    conv_lhs => rw [hxa]
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, e1, mul_smul]
  have keyM : ∀ (M : M4 A) (Y : κ → sp4 (ResidueField O)) (g : M4 (ResidueField O)),
      M.map p = 0 → (∀ u, (Y u).1 * g = M.map (co u)) →
      M.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ := fun M Y g h1 h3 => by
    ext a b
    have h4 : p (M a b) = 0 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply, key _ h4, Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Submodule.coe_smul, smul_mul_assoc, h3]
    rfl
  have m3 : ∀ d, p'' (μ d) = 0 := fun d => by
    obtain ⟨a, rfl⟩ := residue_surjective d
    rw [m1, map_smul, hη0, smul_zero]
  have hp'' : Function.Surjective p'' := fun y => by
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p' x, pp x⟩
  have hs' : maximalIdeal A' * RingHom.ker p'' = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨y, rfl⟩ := hp' y
    rw [RingHom.mem_ker, pp] at hy
    rw [Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]
  obtain ⟨D', f1, f2⟩ := hD A' p' p'' hpp
  refine ⟨hp'', hs', X1.obCor loc hloc p'' hp'' hs' ν r n hν hw hr rb nb hb hrb hnb D' μ μ.map_add m2 m3 _ hx
    (fun s t => ?_) (fun v s => ?_)⟩
  · rw [f1, keyM _ (fun u => (z u).1 (s, t)) _ (d1 s t) fun u => z1 u s t, Prod.fst_sum, Finset.sum_apply]
    rfl
  · rw [f2, keyM _ (fun u => (z u).2 v s) _ (d2 v s) fun u => z2 u v s, Prod.snd_sum, Finset.sum_apply,
      Finset.sum_apply]
    rfl
end
