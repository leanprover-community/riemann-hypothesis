import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_bound_of_isRoot_exp_mul_forall :
    ∀ (d : ℕ) (p : ℝ → ℂ[X]), (∀ t, p t ≠ 0 ∧ (p t).natDegree ≤ d) → ∃ M : ℝ, ∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M := by
  intro d p hp
  classical
  have hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))} := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    obtain ⟨R, hR⟩ := (F.finite_toSet.isBounded).exists_norm_le
    set S : ℝ := |R| + 1 with hS
    have hSpos : 0 < S := by positivity
    have hRS : ∀ z ∈ F, ‖z‖ ≤ S := fun z hz => by
      have h1 := hR z (Finset.mem_coe.mpr hz)
      have h2 := le_abs_self R
      linarith
    set t : ℝ := S⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hSpos
    have hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1 := fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]
      rw [mul_inv_le_iff₀ hSpos, one_mul]
      exact hRS z hz
    have hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F := by
      intro z hz w hw h
      obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have h1 := hn z hz
      have h2 := hn w hw
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2 := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t := by rw [hn']; ring
        rw [this]
        have := norm_sub_le (z * (t : ℂ)) (w * t)
        linarith
      have hn0 : n = 0 := by
        by_contra hne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
          simp [abs_of_pos Real.pi_pos]
        have h6 := Real.pi_gt_three
        rw [h5] at h3
        nlinarith
      rw [hn0] at hn'
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have : z * (t : ℂ) = w * t := by simpa using hn'
      exact mul_right_cancel₀ htne this
    have hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj, hcard] at hle
    have := (hp t).2
    omega
  obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
  exact ⟨M, fun z hz => hM z hz⟩
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (D : Module.End ℂ E) (M : ℝ), (∀ x y, inner ℂ (D x) y + inner ℂ x (D y) = 0) → (∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ D M hskew hev x
  have hT : (Complex.I • D : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    have h := hskew x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
    linear_combination (-Complex.I) * h
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  have hb : ∀ i, |hT.eigenvalues hn i| ≤ M := by
    intro i
    have h1 := hT.apply_eigenvectorBasis hn i
    have h2 : D (hT.eigenvectorBasis hn i) = (-Complex.I * (hT.eigenvalues hn i : ℂ)) • hT.eigenvectorBasis hn i := by
      have h3 : D (hT.eigenvectorBasis hn i) = (-Complex.I) • ((Complex.I • D : E →ₗ[ℂ] E) (hT.eigenvectorBasis hn i)) := by
        rw [LinearMap.smul_apply, smul_smul]; simp
      rw [h3, h1, smul_smul]; rfl
    have h4 : D.HasEigenvalue (-Complex.I * (hT.eigenvalues hn i : ℂ)) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 h2, (hT.eigenvectorBasis hn).orthonormal.ne_zero i⟩
    have h5 := hev _ h4
    simpa using h5
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb ⟨0, Module.finrank_pos⟩)
  have hDx : ‖D x‖ = ‖(Complex.I • D : E →ₗ[ℂ] E) x‖ := by
    simp [norm_smul]
  rw [hDx, ← (hT.eigenvectorBasis hn).repr.norm_map ((Complex.I • D : E →ₗ[ℂ] E) x),
    ← (hT.eigenvectorBasis hn).repr.norm_map x]
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h6 := hT.eigenvectorBasis_apply_self_apply hn x i
  rw [h6, norm_mul, mul_pow]
  gcongr
  simpa using hb i
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_generator_le_of_polynomial_annihilated :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (u : ℝ → Module.End ℂ E) (D : Module.End ℂ E) (p : ℝ → ℂ[X]) (M : ℝ), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → (∀ x, HasDerivAt (fun t : ℝ => u t x) (D x) 0) → (∀ t, aeval (u t) (p t) = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ u D p M h0 hadd hiso hder hroot hM x
  have hshift : ∀ (t : ℝ) (w : E), HasDerivAt (fun s : ℝ => u s w) (u t (D w)) t := by
    intro t w
    let L : E →L[ℂ] E := LinearMap.toContinuousLinearMap (u t)
    let LR : E →L[ℝ] E := L.restrictScalars ℝ
    have h1 : HasDerivAt (fun s : ℝ => LR (u s w)) (LR (D w)) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 (hder w)
    have h2 : HasDerivAt (fun s : ℝ => LR (u (s - t) w)) (LR (D w)) t := by
      apply HasDerivAt.comp_sub_const t t (f := fun s : ℝ => LR (u s w))
      simpa using h1
    have h3 : (fun s : ℝ => LR (u (s - t) w)) = fun s => u s w := by
      funext s
      show u t (u (s - t) w) = u s w
      rw [← Module.End.mul_apply, ← hadd]
      congr 2
      ring
    rw [h3] at h2
    exact h2
  have hinner : ∀ (t : ℝ) (a b : E), inner ℂ (u t a) (u t b) = inner ℂ a b := by
    intro t a b
    exact LinearIsometry.inner_map_map (⟨u t, hiso t⟩ : E →ₗᵢ[ℂ] E) a b
  have h0' : ∀ a : E, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hskew : ∀ a b : E, inner ℂ (D a) b + inner ℂ a (D b) = 0 := by
    intro a b
    have h1 := (hder a).inner ℂ (hder b)
    have h2 : (fun t : ℝ => inner ℂ (u t a) (u t b)) = fun _ => inner ℂ a b := by
      funext t
      exact hinner t a b
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ a b))
    rw [h0', h0'] at h3
    rw [add_comm]
    exact h3
  have hev : ∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_hasEigenvector
    have hDw : D w = z • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    have hconst : ∀ t : ℝ, Complex.exp (-(z * t)) • u t w = w := by
      have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)) • u s w) 0 t := by
        intro t
        have he : HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)))
            (Complex.exp (-(z * t)) * (-z)) t := by
          have hl : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-z) t := by
            have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
              simpa using (hasDerivAt_id t).ofReal_comp
            have h2 := h.const_mul (-z)
            simpa [neg_mul] using h2
          exact hl.cexp
        have h1 := he.smul (hshift t w)
        have h2 : Complex.exp (-(z * t)) • u t (D w) + (Complex.exp (-(z * t)) * (-z)) • u t w = 0 := by
          rw [hDw, map_smul, smul_smul, ← add_smul]
          have : Complex.exp (-(z * t)) * z + Complex.exp (-(z * t)) * (-z) = 0 := by ring
          rw [this, zero_smul]
        rw [h2] at h1
        exact h1
      intro t
      have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => Complex.exp (-(z * s)) • u s w)
        (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
      simpa [h0'] using hc
    have hut : ∀ t : ℝ, u t w = Complex.exp (z * t) • w := by
      intro t
      have h1 := congrArg (fun v => Complex.exp (z * t) • v) (hconst t)
      simp only [smul_smul] at h1
      rw [← Complex.exp_add] at h1
      simpa using h1
    apply hM
    intro t
    have hvec : (u t).HasEigenvector (Complex.exp (z * t)) w :=
      ⟨Module.End.mem_eigenspace_iff.2 (hut t), hw0⟩
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p t) hvec
    rw [hroot t] at h1
    have h2 : (p t).eval (Complex.exp (z * t)) • w = 0 := by
      rw [← h1]
      rfl
    exact (smul_eq_zero.1 h2).resolve_right hw0
  exact UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound E D M hskew hev x
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : ℝ → H →L[ℂ] H) (p : ℝ → ℂ[X]) (M : ℝ) (v y : H), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => u t v)) → HasDerivAt (fun t : ℝ => u t v) y 0 → (∀ t, aeval (u t) (p t) v = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ‖y‖ ≤ M * ‖v‖ := by
  intro H _ _ u p M v y h0 hadd hiso hfin hy hp hM
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ (Set.range fun t => u t v) := ⟨_, rfl⟩
  rw [← hE] at hfin
  haveI : FiniteDimensional ℂ E := hfin
  have hcomm : ∀ s t x, u s (u t x) = u t (u s x) := by
    intro s t x
    have h : u s * u t = u t * u s := by rw [← hadd, ← hadd, add_comm]
    exact DFunLike.congr_fun h x
  have h0' : ∀ a, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hstab : ∀ s, ∀ x ∈ E, u s x ∈ E := by
    intro s x hx
    rw [hE] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨s + t, by simp [hadd]⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  have hvE : v ∈ E := by
    rw [hE]
    exact Submodule.subset_span ⟨0, h0' v⟩
  have hclosed : IsClosed (E : Set H) := Submodule.closed_of_finiteDimensional E
  have hlim : ∀ w ∈ E, ∀ d, HasDerivAt (fun t : ℝ => u t w) d 0 → d ∈ E := by
    intro w hw d hd
    have ht := hasDerivAt_iff_tendsto_slope.1 hd
    refine hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (E.restrictScalars ℝ).smul_mem _ (E.sub_mem (hstab t w hw) (hstab 0 w hw))
  have hsh : ∀ (s : ℝ) (w d : H), HasDerivAt (fun t : ℝ => u t w) d 0 →
      HasDerivAt (fun t : ℝ => u t (u s w)) (u s d) 0 := by
    intro s w d hd
    let LR : H →L[ℝ] H := (u s).restrictScalars ℝ
    have h1 : HasDerivAt (fun t : ℝ => LR (u t w)) (LR d) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 hd
    have h2 : (fun t : ℝ => LR (u t w)) = fun t => u t (u s w) := by
      funext t
      exact hcomm s t w
    rw [h2] at h1
    exact h1
  have hder : ∀ w ∈ E, ∃ d, HasDerivAt (fun t : ℝ => u t w) d 0 := by
    intro w hw
    rw [hE] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact ⟨u s y, hsh s v y hy⟩
    | zero => exact ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨da, hda⟩ := ha
      obtain ⟨db, hdb⟩ := hb
      refine ⟨da + db, ?_⟩
      convert hda.add hdb using 1
      funext t
      simp
    | smul c a _ ha =>
      obtain ⟨da, hda⟩ := ha
      refine ⟨c • da, ?_⟩
      convert hda.const_smul c using 1
      funext t
      simp
  have hd : ∀ w : E, HasDerivAt (fun t : ℝ => u t (w : H)) (deriv (fun t : ℝ => u t (w : H)) 0) 0 := by
    intro w
    obtain ⟨d, hd⟩ := hder w w.2
    rw [hd.deriv]
    exact hd
  let D : Module.End ℂ E :=
    { toFun := fun w => ⟨deriv (fun t : ℝ => u t (w : H)) 0, hlim _ w.2 _ (hd w)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        refine (hd (a + b)).unique ?_
        convert (hd a).add (hd b) using 1
        · funext t
          simp
        · rfl
      map_smul' := by
        intro c a
        apply Subtype.ext
        refine (hd (c • a)).unique ?_
        convert (hd a).const_smul c using 1
        · funext t
          simp
        · rfl }
  let u' : ℝ → Module.End ℂ E := fun t => (u t : H →ₗ[ℂ] H).restrict (hstab t)
  have hu' : ∀ t (x : E), ((u' t x : E) : H) = u t (x : H) := fun t x => rfl
  have hD : ∀ x : E, ((D x : E) : H) = deriv (fun t : ℝ => u t (x : H)) 0 := fun x => rfl
  have haev : ∀ (t : ℝ) (q : ℂ[X]) (x : E), ((aeval (u' t) q x : E) : H) = aeval (u t) q (x : H) := by
    intro t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul (aeval (u' t)) (C a * X ^ n) X, map_mul (aeval (u t)) (C a * X ^ n) X, aeval_X, aeval_X, Module.End.mul_apply, ContinuousLinearMap.mul_apply, ih, hu']
  have hcq : ∀ (s t : ℝ) (q : ℂ[X]) (x : H), aeval (u t) q (u s x) = u s (aeval (u t) q x) := by
    intro s t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul, aeval_X, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm t s, ih]
  have hkill : ∀ t, ∀ x ∈ E, aeval (u t) (p t) x = 0 := by
    intro t x hx
    rw [hE] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      show aeval (u t) (p t) (u s v) = 0
      rw [hcq, hp, map_zero]
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have hder' : ∀ x : E, HasDerivAt (fun t : ℝ => u' t x) (D x) 0 := by
    intro x
    rw [hasDerivAt_iff_tendsto_slope]
    have h := hasDerivAt_iff_tendsto_slope.1 (hd x)
    rw [tendsto_subtype_rng]
    refine h.congr fun t => ?_
    simp [slope_def_module, hu']
  have hbound := UpperTheory.norm_generator_le_of_polynomial_annihilated E u' D p M
    (by
      ext x
      simp [hu', h0'])
    (by
      intro s t
      ext x
      simp [hu', hadd])
    (by
      intro t x
      exact hiso t x)
    hder'
    (by
      intro t
      ext x
      rw [haev]
      simpa using hkill t x x.2)
    hM ⟨v, hvE⟩
  have hDv : ((D ⟨v, hvE⟩ : E) : H) = y := by
    rw [hD]
    exact hy.deriv
  have hn : ‖D ⟨v, hvE⟩‖ = ‖y‖ := by
    rw [← hDv]
    rfl
  rw [hn] at hbound
  exact hbound
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem pow_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (k : archCompact K n) (m : ℕ) :
    ∀ φ ∈ centralCuspForms K n, (archRepT μ (k : archGroup K n) ^ m) (cuspVecL μ φ) =
      cuspVecL μ (((gkModuleCusp K n).σ k ^ m) φ) := by
  induction m with
  | zero =>
    intro φ _
    simp
  | succ m ih =>
    intro φ hφ
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ← cuspToL2_sigma μ k hφ,
      ih _ (σ_mem_centralCuspForms k hφ)]

private theorem aeval_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n))
    [μ.IsHaarMeasure] (k : archCompact K n) (q : ℂ[X]) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) :
    aeval (archRepT μ (k : archGroup K n)) q (cuspVecL μ φ) =
      cuspVecL μ (aeval ((gkModuleCusp K n).σ k) q φ) := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add, ContinuousLinearMap.add_apply, LinearMap.add_apply, ha, hb]
  | monomial m c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, ContinuousLinearMap.mul_apply,
      pow_cuspVecL μ k m φ hφ]
    simp [Algebra.algebraMap_eq_smul_one]

theorem UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (d : ℕ) (p : archCompact K n → ℂ[X]) (Y : (isExpLieAlgebra K n).lieSubalgebra), (∀ k, p k ≠ 0 ∧ (p k).natDegree ≤ d) → (∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y) ∈ archCompact K n) → ∃ M : ℝ, ∀ φ ∈ centralCuspForms K n, (∀ k, aeval ((gkModuleCusp K n).σ k) (p k) φ = 0) → ‖cuspVecL μ ((gkModuleCusp K n).ρ Y φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
  intro K _ _ n μ _ d p Y hp hk
  let kk : ℝ → archCompact K n := fun t => ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y), hk t⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_isRoot_exp_mul_forall d (fun t => p (kk t)) (fun t => hp _)
  refine ⟨M, fun φ hφ hkill => ?_⟩
  have hy := (isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) (isSmoothVector_cuspToL2 μ hφ)
    ((isExpLieAlgebra K n).ofLie Y)
  have e := derivOp_cuspVecL μ hφ ((isExpLieAlgebra K n).ofLie Y)
  rw [IsExpLieAlgebra.toLie_ofLie] at e
  rw [e] at hy
  have hu : ∀ t : ℝ, (archRepT μ ((kk t : archCompact K n) : archGroup K n)) =
      archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) := fun t => rfl
  refine UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated (CuspL2 μ)
    (fun t => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)))
    (fun t => p (kk t)) M (cuspVecL μ φ) _ ?_ ?_ ?_ ?_ hy ?_ hM
  · ext1 x
    simp [(isExpLieAlgebra K n).expG_zero]
  · intro s t
    ext1 x
    rw [(isExpLieAlgebra K n).expG_add_smul, BanachRep.map_mul_apply]
    rfl
  · intro t x
    rw [archRepT_apply]
    exact UnitaryRep.norm_map _ _ _
  · have hfin := (gkModuleCusp K n).locallyFinite φ
    have hle : Submodule.span ℂ (Set.range fun t : ℝ =>
        archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) (cuspVecL μ φ)) ≤
        (Submodule.span ℂ (Set.range fun k => (gkModuleCusp K n).σ k φ)).map (cuspVecL μ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨kk t, rfl⟩, cuspToL2_sigma μ (kk t) hφ⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro t
    have := aeval_cuspVecL μ (kk t) (p (kk t)) hφ
    rw [hkill, map_zero] at this
    exact this
end
