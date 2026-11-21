import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_sections_finite_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), IsUnf U → ∀ Z : Comp Xo c, ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (t : Formalism.L2.Pj.Ix Dw → (Om Z)ˣ), (∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f ∈ R) ∧ ∀ φ : R →+* ℂ, φ.comp (algebraMap c.F R) = σ → ∃ z ∈ framesOn U Z, ∃ s : Formalism.L2.Pj.Ix Dw → ℂˣ, ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ∀ b : R, (b : Om Z) = ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f → φ b = ((∏ i, s i ^ e i : ℂˣ) : ℂ) * rdU U f z.1 z.2 := by
  first | exact @GlobalTheory.DegCmp.exists_chart_read_at_frames | exact GlobalTheory.DegCmp.exists_chart_read_at_frames | (intros; apply GlobalTheory.DegCmp.exists_chart_read_at_frames <;> assumption)
end

section
section
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open Polynomial

theorem le_sqrt_mul_pow_of_sq_le {n : ℕ} (τ : ℕ) (x y C : ℝ) (u : Fin n → ℝ) (hx : 0 ≤ x) (hu : ∀ i, 0 ≤ u i)
    (h : y ^ 2 ≤ C * (∑ i, u i ^ 2) ^ τ) :
    x ^ τ * y ≤ Real.sqrt (max C 0) * (1 + ∑ i, x * u i) ^ τ := by
  have hS : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
  have h1 : ∑ i, u i ^ 2 ≤ (∑ i, u i) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hu i
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : y ^ 2 ≤ (Real.sqrt (max C 0) * (∑ i, u i) ^ τ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm τ 2, pow_mul]
    exact h.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 h1 τ) (pow_nonneg h0 τ) (le_max_right _ _))
  have h3 : y ≤ Real.sqrt (max C 0) * (∑ i, u i) ^ τ :=
    (abs_le_of_sq_le_sq' h2 (by positivity)).2
  calc x ^ τ * y ≤ x ^ τ * (Real.sqrt (max C 0) * (∑ i, u i) ^ τ) := by gcongr
    _ = Real.sqrt (max C 0) * (∑ i, x * u i) ^ τ := by rw [← Finset.mul_sum, mul_pow]; ring
    _ ≤ Real.sqrt (max C 0) * (1 + ∑ i, x * u i) ^ τ := by
      have : 0 ≤ ∑ i, x * u i := Finset.sum_nonneg fun i _ => mul_nonneg hx (hu i)
      gcongr
      linarith

theorem isIntDeg_of_bounded_of_algHom (K V Ω R : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] (ι : R →ₐ[K] Ω) (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V)
    (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ) (hw : ∀ i, ι (w' i) = (a : Ω) * ev (w i))
    (ht : ι t' = (a : Ω) ^ τ * t)
    (hb : ∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) :
    IsIntDeg ev τ t := by
  have hint : IsIntegral (Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)))
      (X ^ τ * Polynomial.C t' : Polynomial R) := by
    refine GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.2 K (Polynomial R) σ n τ _ _ (Real.sqrt (max C 0)) fun φ hφ => ?_
    have h := hb (φ.comp Polynomial.C) hφ
    simp only [map_mul, map_pow, norm_mul, norm_pow]
    exact le_sqrt_mul_pow_of_sq_le τ _ _ C (fun i => ‖φ (Polynomial.C (w' i))‖) (norm_nonneg _)
      (fun _ => norm_nonneg _) h
  let f : Polynomial R →ₐ[K] Polynomial Ω :=
    Polynomial.eval₂AlgHom ((Polynomial.CAlgHom : Ω →ₐ[K] Polynomial Ω).comp ι) (X * Polynomial.C ((a⁻¹ : Ωˣ) : Ω))
      fun _ => Commute.all _ _
  have hfX : f X = X * Polynomial.C ((a⁻¹ : Ωˣ) : Ω) := by simp [f]
  have hfC : ∀ b : R, f (Polynomial.C b) = Polynomial.C (ι b) := fun b => by simp [f]
  have hfw : ∀ i, f (X * Polynomial.C (w' i)) = X * Polynomial.C (ev (w i)) := fun i => by
    rw [map_mul, hfX, hfC, hw, mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hft : f (X ^ τ * Polynomial.C t') = X ^ τ * Polynomial.C t := by
    rw [map_mul, map_pow, hfX, hfC, ht, mul_pow, mul_assoc, ← map_pow, ← map_mul, ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have hmem : ∀ x ∈ Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)), f x ∈ coneAlg ev := by
    intro x hx
    have : Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)) ≤ (coneAlg ev).comap f := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      change f _ ∈ coneAlg ev
      rw [hfw]
      exact Algebra.subset_adjoin ⟨w i, rfl⟩
    exact this hx
  rw [IsIntDeg, ← hft]
  exact hint.map_of_comp_eq
    ((f.toRingHom.comp (Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R))).val.toRingHom).codRestrict
      (coneAlg ev) fun x => hmem x.1 x.2) f.toRingHom (RingHom.ext fun _ => rfl)

theorem isIntDeg_of_bounded (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (R : Subalgebra K Ω) [Algebra.FiniteType K R] (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V)
    (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ) (hw : ∀ i, (w' i : Ω) = (a : Ω) * ev (w i))
    (ht : (t' : Ω) = (a : Ω) ^ τ * t)
    (hb : ∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) :
    IsIntDeg ev τ t :=
  isIntDeg_of_bounded_of_algHom K V Ω R ev R.val σ a n τ w w' t t' C hw ht hb

end GlobalTheory.DegCmp
end

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_degree_of_norm_bound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (R : Subalgebra K Ω) [Algebra.FiniteType K R] (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V) (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ), (∀ i, (w' i : Ω) = (a : Ω) * ev (w i)) → (t' : Ω) = (a : Ω) ^ τ * t → (∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) → IsIntDeg ev τ t := by
  atlas_forward_decl GlobalTheory.DegCmp.isIntDeg_of_bounded
end

section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal

namespace GlobalTheory.DegTop

theorem growth_mono (D : ℕ) {s s' : ℕ → ℕ∞} (h : ∀ k, 1 ≤ k → s k ≤ s' k) : growth D s ≤ growth D s' :=
  Filter.limsup_le_limsup ((Filter.eventually_ge_atTop 1).mono fun k hk => ENNReal.div_le_div_right
    (mul_le_mul_right (ENat.toENNReal_le.2 (h k hk)) _) _)

theorem growth_top (D : ℕ) : growth D (fun _ => ⊤) = ⊤ := by
  rw [growth, ← Filter.limsup_const (f := (Filter.atTop : Filter ℕ)) (⊤ : ℝ≥0∞)]
  refine Filter.limsup_congr (Filter.Eventually.of_forall fun k => ?_)
  rw [ENat.toENNReal_top, ENNReal.mul_top (Nat.cast_ne_zero.2 D.factorial_ne_zero)]
  exact ENNReal.top_div_of_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top k))

theorem of_not_finiteDimensional {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : ¬ FiniteDimensional K V) :
    (∃ v : V, v ≠ 0) ∧ Cardinal.aleph0 ≤ Module.rank K V := by
  refine ⟨?_, not_lt.1 fun h2 => h (Module.rank_lt_aleph0_iff.1 h2)⟩
  by_contra h0
  push Not at h0
  have : Subsingleton V := subsingleton_of_forall_eq 0 h0
  exact h inferInstance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem mem_holSub_iff {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem eq_zero_of_genVal {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) :
    f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1 hZ hf.2

theorem mul_mem_cuspOn {Z : Comp Xo c} {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c}
    (hf : f ∈ cuspOn U Z G) (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspOn U Z (G + G') := by
  refine ⟨?_, by rw [mul_comm]; exact mul_mem_suppOn _ hf.2⟩
  have hf' := mem_cuspW.1 hf.1
  rw [mem_cuspW] at hg
  refine mem_cuspW.2 ⟨?_, fun σ hσ => ?_⟩
  · have e : exZ Dw (G + G') = exZ Dw G + exZ Dw G' := funext fun i => exZ_add _ _ _
    rw [e]
    exact mul_mem_secZ hf'.1 hg.1
  · rw [AllWt.rdU_mul, mem_holSub_iff]
    intro k
    rw [modelWt_add (U σ) hG hG' k]
    exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf'.2 σ hσ) k) _
      ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1

omit [NumberField E] [IsCMField E] in

theorem even_nsmul {G : WTZ E} (hG : Even G.2) (n : ℕ) : Even (n • G).2 := by
  rw [Prod.smul_snd, nsmul_eq_mul]; exact hG.mul_left n

theorem range_pow_le {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) (n : ℕ) :
    (LinearMap.range (genPoint Z (cuspOn U Z G))) ^ (n + 1) ≤
      (cuspOn U Z ((n + 1) • G)).map (genVal Z).toLinearMap := by
  induction n with
  | zero =>
    rintro _ hy
    rw [zero_add, pow_one] at hy
    obtain ⟨v, rfl⟩ := hy
    exact ⟨v, by simp, rfl⟩
  | succ n ih =>
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    obtain ⟨f, hf, rfl⟩ := ih ha
    obtain ⟨v, rfl⟩ := hb
    refine ⟨f * v, ?_, map_mul (genVal Z) _ _⟩
    rw [succ_nsmul]
    exact mul_mem_cuspOn (even_nsmul hG _) hG hf v.2.1

theorem hilb_le {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ : ℕ} (hτ : 1 ≤ τ) :
    hilb (genPoint Z (cuspOn U Z G)) τ ≤ Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))) := by
  obtain ⟨n, rfl⟩ : ∃ n, τ = n + 1 := ⟨τ - 1, by omega⟩
  exact OrderHomClass.mono Cardinal.toENat ((Submodule.rank_mono (range_pow_le hG n)).trans (rank_map_le _ _))

theorem rank_map_mul {Z : Comp Xo c} {G : WTZ E} {θ : Rul Xo c} (hθ : genVal Z θ ≠ 0) :
    Module.rank c.F ((cuspOn U Z G).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F θ)) =
      Module.rank c.F (cuspOn U Z G) := by
  have hi : Function.Injective (((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F θ) ∘ₗ (cuspOn U Z G).subtype) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : genVal Z (θ * f) = 0 := hf
    rw [map_mul] at h1
    exact Subtype.ext (eq_zero_of_genVal f.2 ((mul_eq_zero.1 h1).resolve_left hθ))
  rw [← rank_range_of_injective _ hi, LinearMap.range_comp, Submodule.range_subtype]

theorem finiteDimensional_of_growthOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) (h : growthOn U Z G ≠ ⊤) :
    FiniteDimensional c.F (cuspOn U Z G) := by
  by_contra hfd
  obtain ⟨⟨v, hv⟩, hr⟩ := of_not_finiteDimensional hfd
  have hv' : genVal Z (v : Rul Xo c) ≠ 0 := fun h0 => hv (Subtype.ext (eq_zero_of_genVal v.2 h0))
  have key : ∀ n : ℕ, ∀ f ∈ cuspOn U Z G, (v : Rul Xo c) ^ n * f ∈ cuspOn U Z ((n + 1) • G) := fun n f hf => by
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [succ_nsmul, pow_succ, mul_right_comm]
      exact mul_mem_cuspOn (even_nsmul hG _) hG ih v.2.1
  refine h (top_le_iff.1 ((growth_top (dimFlag Dw)).symm.trans_le (growth_mono _ fun k hk => ?_)))
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 : Module.rank c.F (cuspOn U Z G) ≤ Module.rank c.F (cuspOn U Z ((n + 1) • G)) := by
    rw [← rank_map_mul (U := U) (G := G) (θ := (v : Rul Xo c) ^ n) (by rw [map_pow]; exact pow_ne_zero _ hv')]
    refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, key n f hf, rfl⟩
  rw [top_le_iff, Cardinal.toENat_eq_top]
  exact hr.trans h1

theorem topDeg_nonneg (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) : 0 ≤ topDeg U Z u :=
  mul_nonneg (vZero_nonneg U Z) (Int.cast_pos.2 (vdm_pos hu)).le

theorem growth_mul_eq (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {a : ℕ}
    (ha : 1 ≤ a) : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • wtOf Dw u 0)))) =
      ENNReal.ofReal ((a : ℝ) ^ dimFlag Dw * topDeg U Z u) := by
  have h1 : ∀ τ, StrictAnti ((a • u) τ) := fun τ i j hij => by
    have := hu τ hij
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left this (by exact_mod_cast ha)
  have h2 := hP Z (a • u) h1
  have h3 : wtOf Dw (a • u) 0 = a • wtOf Dw u 0 := by rw [nsmul_wtOf, smul_zero]
  have h4 : topDeg U Z (a • u) = (a : ℝ) ^ dimFlag Dw * topDeg U Z u := by
    rw [topDeg, topDeg, ← Nat.cast_smul_eq_nsmul ℤ a u, vdm_smul, dimFlag]
    push_cast; ring
  rw [← h4, ← h2, growthOn, h3]
  exact congrArg _ (funext fun k => by rw [mul_nsmul])

theorem finiteDimensional_cuspOn (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    FiniteDimensional c.F (cuspOn U Z (wtOf Dw u 0)) :=
  finiteDimensional_of_growthOn (even_wtOf u 0) (by rw [hP Z u hu]; exact ENNReal.ofReal_ne_top)

theorem growth_hilb_le (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {a : ℕ}
    (ha : 1 ≤ a) : growth (dimFlag Dw) (fun k => hilb (genPoint Z (cuspOn U Z (wtOf Dw u 0))) (a * k)) ≤
      ENNReal.ofReal ((a : ℝ) ^ dimFlag Dw * topDeg U Z u) :=
  (growth_mono _ fun _ hk => hilb_le (even_wtOf u 0) (Nat.mul_pos ha hk)).trans_eq (growth_mul_eq hP Z hu ha)

theorem compDeg_le (hP : Proport U) (Z : Comp Xo c) {u : Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ topDeg U Z u := by
  rcases (compDeg U Z (wtOf Dw u 0)).eq_zero_or_pos with h0 | h0
  · rw [h0, Nat.cast_zero]; exact topDeg_nonneg Z hu
  · have := finiteDimensional_cuspOn hP Z hu
    have h1 := GlobalTheory.T.cone_degree_growth_chowForm_integrality.1 c.F _ _ _ _ 1 le_rfl _ ((imageDeg_pos_iff _ _).1 h0)
    have h2 := growth_hilb_le hP Z hu le_rfl
    rw [h1, Nat.cast_one, Nat.cast_one, one_pow, one_pow, one_mul, one_mul, ← ENNReal.ofReal_natCast] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (topDeg_nonneg Z hu)).1 h2

def normFac {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (G : WTZ E) (z : Σ k, Frame (U.X k).Ψ r) : ℝ :=
  lieFacZ Dw x G * (U.X z.1).nfac (modelWt U G z.1) z.2

section Fac

variable {σ : c.F →+* ℂ} (U₁ : Unf Xo c σ r) (x)

theorem homN_eq (G : WTZ E) (f : Rul Xo c) (z : Σ k, Frame (U₁.X k).Ψ r) :
    homN U₁ x G f z = normFac U₁ x G z * ‖rdU U₁ f z.1 z.2‖ := by
  show _ * (‖rdU U₁ f z.1 z.2‖ * (U₁.X z.1).nfac (modelWt U₁ G z.1) z.2) = _
  rw [normFac]; ring

theorem normFac_pos (G : WTZ E) {z : Σ k, Frame (U₁.X k).Ψ r} (hz : z.2 ∈ (U₁.X z.1).dom) : 0 < normFac U₁ x G z := by
  have hd : ∀ τ i, dmin (U₁.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  exact mul_pos (lieFacZ_pos _ _) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _)

theorem normFac_add {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {z : Σ k, Frame (U₁.X k).Ψ r}
    (hz : z.2 ∈ (U₁.X z.1).dom) : normFac U₁ x (G + G') z = normFac U₁ x G z * normFac U₁ x G' z := by
  have hd : ∀ τ i, dmin (U₁.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  have key : ∀ la la' : Wt (U₁.X z.1).Ψ r, (U₁.X z.1).nfac (la + la') z.2 =
      (U₁.X z.1).nfac la z.2 * (U₁.X z.1).nfac la' z.2 := fun la la' => by
    unfold Data.nfac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _)))]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [normFac, normFac, normFac, modelWt_add U₁ hG hG', key, lieFacZ_add]
  ring

theorem normFac_nsmul {G : WTZ E} (hG : Even G.2) {z : Σ k, Frame (U₁.X k).Ψ r} (hz : z.2 ∈ (U₁.X z.1).dom) (n : ℕ) :
    normFac U₁ x (n • G) z = normFac U₁ x G z ^ n := by
  induction n with
  | zero =>
    have h := normFac_add x U₁ (G := 0) (G' := 0) Even.zero Even.zero hz
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact (mul_left_cancel₀ (normFac_pos x U₁ 0 hz).ne' (h.symm.trans (mul_one _).symm))
  | succ n ih => rw [succ_nsmul, normFac_add x U₁ (even_nsmul hG n) hG hz, ih, pow_succ]



end Fac

theorem prod_exZ_nsmul {M : Type} [CommGroup M] (t : Formalism.L2.Pj.Ix Dw → M) (G : WTZ E) (n : ℕ) :
    ∏ i, t i ^ exZ Dw (n • G) i = (∏ i, t i ^ exZ Dw G i) ^ n := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : exZ Dw (n • G) i = exZ Dw G i * n := by
    rcases i with _ | i <;> simp [exZ, mul_comm]
  rw [this, zpow_mul, zpow_natCast]





end GlobalTheory.DegTop
end
end
