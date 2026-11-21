import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j
        simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd


end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : E), IsIntegral ℤ u →
      u * IsCMField.complexConj E u = 1 → ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  intro E _ _ _ u hu h
  have hn : ∀ s : E →+* ℂ, ‖s u‖ = 1 := by
    intro s
    have h1 : s u * (starRingEnd ℂ) (s u) = 1 := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, h, map_one]
    have h2 : ‖s u‖ ^ 2 = 1 := by
      have := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      rw [sq, this]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hu hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_of_unity_eq_one_of_dvd_sub_one :
    ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E) (n M : ℕ),
      0 < n → u ^ n = 1 → 3 ≤ M → (M : 𝓞 E) ∣ u - 1 → u = 1 := by
  intro E _ _ u n M hn hu hM ⟨x, hx⟩
  have hlt : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ < 1 := by
    intro φ
    have h1 : (φ (u : E)) ^ n = 1 := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hu
      simpa using this
    have h2 : ‖φ (u : E)‖ = 1 := by
      have := congrArg norm h1
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h3 : φ (u : E) - 1 = (M : ℂ) * φ (x : E) := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hx
      simpa using this
    have h4 : (M : ℝ) * ‖φ (x : E)‖ ≤ 2 := by
      have h5 := norm_sub_le (φ (u : E)) 1
      rw [h3, norm_mul, h2, norm_one, Complex.norm_natCast] at h5
      linarith
    have h6 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (x : E))]
  by_contra hne
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have : x = 0 := by exact_mod_cast h0
    rw [this, mul_zero, sub_eq_zero] at hx
    exact hne hx
  obtain ⟨k, hk, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0
    (RingOfIntegers.isIntegral_coe x) (fun φ => (hlt φ).le)
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h7 := congrArg (fun y : E => ‖φ y‖) hpow
  simp only [map_pow, norm_pow, map_one, norm_one] at h7
  have h8 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h7
  exact (hlt φ).ne h8

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_mul_complexConj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (x : E) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x * IsCMField.complexConj E x = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  have h1 : ‖φ x‖ = 1 := by
    have h : ‖φ x‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h1]
  simp

theorem root_eq_one_of_halfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (I : Ideal (𝓞 E)) (M : ℕ), 3 ≤ M → I * I.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)} → I ⊔ I.map (bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ (u : 𝓞 E) (n : ℕ), 0 < n → u ^ n = 1 → u - 1 ∈ I → u = 1 := by
  intro E _ _ _ bar hbar I M hM hI hco u n hn hu h1
  have hub : u * bar u = 1 := by
    apply RingOfIntegers.ext
    have hx : (u : E) ^ n = 1 := by
      have := congrArg (fun a : 𝓞 E => (a : E)) hu
      simpa using this
    have := root_mul_complexConj_eq_one (u : E) n hn hx
    rw [← hbar] at this
    simpa using this
  have h2 : bar u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) h1
    simpa using this
  have h3 : u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have e : u - 1 = (-u) * (bar u - 1) := by linear_combination hub
    rw [e]
    exact Ideal.mul_mem_left _ _ h2
  have h4 : u - 1 ∈ Ideal.span {(M : 𝓞 E)} := by
    rw [← hI, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 hco)]
    exact ⟨h1, h3⟩
  exact GlobalTheory.CompanionTheory.Ar.Flat.root_of_unity_eq_one_of_dvd_sub_one E u n M hn hu hM (Ideal.mem_span_singleton.1 h4)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_one_add_comp_comm_field {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (A : V →ₗ[K] W) (B : W →ₗ[K] V) :
    LinearMap.det (1 + A ∘ₗ B) = LinearMap.det (1 + B ∘ₗ A) := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bV, map_add, map_add,
    LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_comp bV bW bV,
    LinearMap.toMatrix_one, LinearMap.toMatrix_one, Matrix.det_one_add_mul_comm]

theorem exists_det_congr_one : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] (I : Ideal (𝓞 E)) (g : La →ₗ[𝓞 E] La), (∀ a, g a - a ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∃ u : 𝓞 E, u - 1 ∈ I ∧ (u : E) = LinearMap.det (g.baseChange E) := by
  intro E _ _ La _ _ _ _ I g hg
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) La
  set N : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → 𝓞 E) := i ∘ₗ ((g - 1) ∘ₗ p) with hN
  have key : ∀ (x : La), x ∈ I • (⊤ : Submodule (𝓞 E) La) → ∀ k, i x k ∈ I := by
    intro x hx k
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x y hx hy
      rw [map_add, Pi.add_apply]
      exact I.add_mem hx hy
  refine ⟨LinearMap.det (1 + N), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, ← LinearMap.det_toMatrix', RingHom.map_det, map_one]
    have : (Ideal.Quotient.mk I).mapMatrix (LinearMap.toMatrix' (1 + N)) = 1 := by
      rw [map_add, map_add, LinearMap.toMatrix'_one, map_one, add_eq_left]
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
        LinearMap.toMatrix'_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact key _ (hg _) _
    rw [this, Matrix.det_one]
  · have h1 : ((LinearMap.det (1 + N) : 𝓞 E) : E) = LinearMap.det ((1 + N).baseChange E) :=
      (LinearMap.det_baseChange (A := E) (1 + N)).symm
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_one, hN, LinearMap.baseChange_comp,
      det_one_add_comp_comm_field, ← LinearMap.baseChange_comp, LinearMap.comp_assoc, hpi,
      LinearMap.comp_id, LinearMap.baseChange_sub, LinearMap.baseChange_one, add_sub_cancel]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem perDet_trace_mul_ext {E : Type} [Field E] [NumberField E] (u v : E)
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) : u = v := by
  have hnd := traceForm_nondegenerate ℚ E
  apply ((Algebra.traceForm ℚ E).toDual hnd).injective
  apply (integralBasis E).ext
  intro i
  simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply, integralBasis_apply] using
    h (RingOfIntegers.basis E i)

theorem perDet_exists_herm {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (x y : La) :
    ∃ u : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (u * a) = ((EF (a • x) y : ℤ) : ℚ) := by
  have hnd := traceForm_nondegenerate ℚ E
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ
    (fun i => ((EF (RingOfIntegers.basis E i • x) y : ℤ) : ℚ))
  obtain ⟨u, hu⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective f
  refine ⟨u, fun a => ?_⟩
  have h1 : Algebra.trace ℚ E (u * a) = f a := by
    have := LinearMap.congr_fun hu (a : E)
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using this
  rw [h1]
  let L1 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom)
  let L2 : 𝓞 E →ₗ[ℤ] ℚ := AddMonoidHom.toIntLinearMap
    { toFun := fun a => ((EF (a • x) y : ℤ) : ℚ)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul] }
  have hL : L1 = L2 := by
    apply (RingOfIntegers.basis E).ext
    intro i
    have hb : (algebraMap (𝓞 E) E) (RingOfIntegers.basis E i) = integralBasis E i :=
      (integralBasis_apply E i).symm
    change f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [hb]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun hL a

theorem perDet_exists_clear {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (v : E ⊗[𝓞 E] La) :
    ∃ (c : 𝓞 E) (x : La), c ≠ 0 ∧ ((c : E)) • v = (1 : E) ⊗ₜ[𝓞 E] x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul e x =>
    obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    have hcE : (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc0
    refine ⟨c, b • x, hc0, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      smul_eq_mul, Algebra.smul_def (A := E) b (1 : E)]
    congr 1
    change algebraMap (𝓞 E) E c * _ = _
    field_simp
  | add v w hv hw =>
    obtain ⟨c, x, hc, hx⟩ := hv
    obtain ⟨d, y, hd, hy⟩ := hw
    refine ⟨c * d, d • x + c • y, mul_ne_zero hc hd, ?_⟩
    have hsm : ∀ (r : 𝓞 E) (t : La), (1 : E) ⊗ₜ[𝓞 E] (r • t) = ((r : E)) • ((1 : E) ⊗ₜ[𝓞 E] t) := by
      intro r t
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one, Algebra.smul_def, _root_.mul_one]
    rw [TensorProduct.tmul_add, hsm, hsm, ← hx, ← hy, smul_add, smul_smul, smul_smul]
    push_cast
    congr 2 <;> ring_nf

theorem perDet_det_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (EF : LinearMap.BilinForm ℤ La) (hinj : Function.Injective EF)
    (adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (bar a • y))
    (g : La →ₗ[𝓞 E] La) (hg : ∀ a b, EF (g a) (g b) = EF a b) :
    LinearMap.det (g.baseChange E) * IsCMField.complexConj E (LinearMap.det (g.baseChange E)) = 1 := by
  classical
  choose h hh using perDet_exists_herm (E := E) EF
  let σ : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hσ : ∀ c : 𝓞 E, σ (c : E) = ((bar c : 𝓞 E) : E) := fun c => (hbar c).symm
  have hbb : ∀ c : 𝓞 E, bar (bar c) = c := by
    intro c
    apply RingOfIntegers.ext
    rw [hbar, hbar]
    exact IsCMField.complexConj_apply_apply E _
  have h_add_l : ∀ x x' y, h (x + x') y = h x y + h x' y := fun x x' y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, smul_add, map_add, LinearMap.add_apply]
      push_cast
      rfl
  have h_add_r : ∀ x y y', h x (y + y') = h x y + h x y' := fun x y y' =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, map_add]
      push_cast
      rfl
  have h_smul_l : ∀ (c : 𝓞 E) x y, h (c • x) y = (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : (c : E) * h x y * (a : E) = h x y * ((a * c : 𝓞 E) : E) := by
        push_cast; ring
      rw [e1, hh, hh, smul_smul]
  have h_smul_r : ∀ (c : 𝓞 E) x y, h x (c • y) = σ (c : E) * h x y := fun c x y =>
    perDet_trace_mul_ext _ _ fun a => by
      have e1 : σ (c : E) * h x y * (a : E) = h x y * ((bar c * a : 𝓞 E) : E) := by
        rw [hσ]; push_cast; ring
      rw [e1, hh, hh, ← smul_smul, adj (bar c), hbb]
  have h_iso : ∀ x y, h (g x) (g y) = h x y := fun x y =>
    perDet_trace_mul_ext _ _ fun a => by
      rw [hh, hh, ← map_smul, hg]
  let f : La → (La →ₗ[𝓞 E] E) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => h_add_l x x' y
      map_smul' := fun c x => by
        rw [h_smul_l, RingHom.id_apply, Algebra.smul_def] }
  let F : La → ((E ⊗[𝓞 E] La) →ₗ[E] E) := fun y => LinearMap.liftBaseChange E (f y)
  have F_tmul : ∀ y (e : E) x, F y (e ⊗ₜ[𝓞 E] x) = e * h x y := by
    intro y e x
    simp only [F, LinearMap.liftBaseChange_tmul, smul_eq_mul]
    rfl
  have F_add : ∀ y y', F (y + y') = F y + F y' := by
    intro y y'
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x => rw [LinearMap.add_apply, F_tmul, F_tmul, F_tmul, h_add_r, mul_add]
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  have F_smul : ∀ (c : 𝓞 E) y, F (c • y) = σ (c : E) • F y := by
    intro c y
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul e x =>
      rw [LinearMap.smul_apply, F_tmul, F_tmul, h_smul_r, smul_eq_mul]
      ring
    | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
  let f0 : E →+ La →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := AddMonoidHom.mk'
    (fun e => AddMonoidHom.mk' (fun y => σ e • F y) (fun y y' => by rw [F_add, smul_add]))
    (fun e e' => by
      ext y : 1
      simp [add_smul])
  let G : (E ⊗[𝓞 E] La) →+ ((E ⊗[𝓞 E] La) →ₗ[E] E) := TensorProduct.liftAddHom f0
    (fun r e y => by
      change σ (r • e) • F y = σ e • F (r • y)
      rw [F_smul, smul_smul, Algebra.smul_def, map_mul, _root_.mul_comm])
  have G_tmul : ∀ (e : E) y, G (e ⊗ₜ[𝓞 E] y) = σ e • F y := fun e y => rfl
  have G_smul : ∀ (c : E) w, G (c • w) = σ c • G w := by
    intro c w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul e y =>
      rw [TensorProduct.smul_tmul', G_tmul, G_tmul, smul_eq_mul, map_mul, smul_smul]
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]
  let Hf : (E ⊗[𝓞 E] La) →ₗ[E] (E ⊗[𝓞 E] La) →ₛₗ[σ] E :=
    LinearMap.mk₂'ₛₗ (RingHom.id E) σ (fun v w => G w v)
      (fun v v' w => map_add _ _ _)
      (fun c v w => by rw [map_smul]; rfl)
      (fun v w w' => by rw [map_add, LinearMap.add_apply])
      (fun c v w => by rw [G_smul, LinearMap.smul_apply])
  have hHf : ∀ v w, Hf v w = G w v := fun _ _ => rfl
  have hnd : ∀ v, (∀ w, Hf v w = 0) → v = 0 := by
    intro v hv
    obtain ⟨c, x, hc, hx⟩ := perDet_exists_clear v
    have hcE : (c : E) ≠ 0 := by simpa using hc
    have h0 : ∀ y, h x y = 0 := by
      intro y
      have h1 := hv ((1 : E) ⊗ₜ[𝓞 E] y)
      rw [hHf, G_tmul, map_one, one_smul] at h1
      have h2 : F y ((c : E) • v) = 0 := by rw [map_smul, h1, smul_zero]
      rw [hx, F_tmul, _root_.one_mul] at h2
      exact h2
    have hx0 : x = 0 := by
      apply hinj
      rw [map_zero]
      ext y
      have h3 := hh x y 1
      rw [h0 y] at h3
      simpa using h3.symm
    rw [hx0, TensorProduct.tmul_zero] at hx
    exact (smul_eq_zero.1 hx).resolve_left hcE
  have hiso : ∀ v w, Hf (g.baseChange E v) (g.baseChange E w) = Hf v w := by
    intro v w
    rw [hHf, hHf]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha, hb]
    | tmul e y =>
      rw [LinearMap.baseChange_tmul, G_tmul, G_tmul, LinearMap.smul_apply, LinearMap.smul_apply]
      congr 1
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | tmul e' x => rw [LinearMap.baseChange_tmul, F_tmul, F_tmul, h_iso]
  exact det_mul_map_det_eq_one_of_sesq σ Hf hnd (g.baseChange E) hiso

theorem per_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (gam : D.La ≃ₗ[𝓞 E] D.La), (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam a = a + l.M • e) → LinearMap.det ((gam : D.La →ₗ[𝓞 E] D.La).baseChange E) = 1 := by
  intro E _ _ _ H D l gam hiso hlev
  haveI := D.fin
  haveI := D.proj
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← l.prod] at h1
    have h2 : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact h2 h1
  have h1mem : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨m', hm', m, hm, hmm⟩ := Submodule.mem_sup.1 h1mem
  have hcong : ∀ a, (gam : D.La →ₗ[𝓞 E] D.La) a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
    intro a
    obtain ⟨e, he⟩ := hlev (m • a) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have h1 : m • gam a = m • a + ((l.M : ℕ) : 𝓞 E) • e := by
      rw [← map_smul, he, Nat.cast_smul_eq_nsmul]
    have h3 : gam a - a = m' • (gam a - a) + m • (gam a - a) := by
      rw [← add_smul, hmm, one_smul]
    have h4 : m • (gam a - a) = ((l.M : ℕ) : 𝓞 E) • e := by
      rw [smul_sub, h1, add_sub_cancel_left]
    rw [h4] at h3
    change gam a - a ∈ _
    rw [h3]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hm' Submodule.mem_top)
      (Submodule.smul_mem_smul hM Submodule.mem_top)
  obtain ⟨u, hu1, hu2⟩ := exists_det_congr_one E D.La l.Mb (gam : D.La →ₗ[𝓞 E] D.La) hcong
  have hdet := perDet_det_mul_conj H.bar H.bar_eq D.EF D.unimod.1 D.adj
    (gam : D.La →ₗ[𝓞 E] D.La) hiso
  rw [← hu2] at hdet ⊢
  obtain ⟨n, hn, hun⟩ := pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one E (u : E)
    (RingOfIntegers.isIntegral_coe u) hdet
  have hun' : u ^ n = 1 := RingOfIntegers.ext (by simpa using hun)
  have hu : u = 1 := root_eq_one_of_halfLevel E H.bar H.bar_eq l.Mb l.M l.three_le l.prod l.coprime
    u n hn hun' hu1
  rw [hu]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat
end
