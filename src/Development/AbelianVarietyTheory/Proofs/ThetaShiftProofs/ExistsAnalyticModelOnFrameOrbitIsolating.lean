import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BetaPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PeriodMapIntegerVector
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.Isolate

section Tr
variable {E : Type} [Field E] [NumberField E]

theorem trace_re (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : E →+* ℂ, (τ z).re := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ τ : E →+* ℂ, τ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun _ => rfl)).symm
  rw [h2] at h
  have := congrArg Complex.re h
  simpa [Complex.re_sum] using this

theorem eq_zero_of_trace (z : E) (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (z * a) = 0) : z = 0 := by
  apply (traceForm_nondegenerate ℚ E).1
  intro y
  rw [← (integralBasis E).sum_repr y]
  simp only [map_sum, map_smul, Algebra.traceForm_apply, integralBasis_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := h (RingOfIntegers.basis E i)
  rw [show (algebraMap (𝓞 E) E) (RingOfIntegers.basis E i) = (RingOfIntegers.basis E i : E) from rfl, this, smul_zero]

theorem exists_den : ∃ D : ℕ, 0 < D ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * a) = m) →
    IsIntegral ℤ ((D : E) * z) := by
  classical
  set d := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) with hd
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image d)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun z hz => ?_⟩
  have key : IsIntegral ℤ ((y : E) * z) := by
    rw [← d.sum_repr z, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    obtain ⟨m, hm⟩ := hz (RingOfIntegers.basis E i)
    have : d.repr z i = m := by
      rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, integralBasis_apply]
      exact hm
    rw [this]
    have h1 := h (d i) (by simp)
    have : (y : E) * ((m : ℚ) • d i) = m • (y • d i) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact h1.zsmul m
  rcases Int.natAbs_eq y with e | e
  · rw [e] at key; simpa using key
  · rw [e] at key
    have := key.neg
    simpa using this

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X)

theorem trace_pairE (x : X) (a : 𝓞 E) :
    Algebra.trace ℚ E (GlobalTheory.ArcQ.pairE (E := E) ξ x * a) = (ξ (a • x) : ℤ) := by
  classical
  have hb : ∀ j, Algebra.trace ℚ E (GlobalTheory.ArcQ.pairE (E := E) ξ x * (RingOfIntegers.basis E j : E)) =
      (ξ ((RingOfIntegers.basis E j) • x) : ℤ) := by
    intro j
    unfold GlobalTheory.ArcQ.pairE
    rw [Finset.sum_mul, map_sum]
    have : ∀ i, Algebra.trace ℚ E ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
        (NumberField.integralBasis E) i * ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : E) *
        (RingOfIntegers.basis E j : E)) = if j = i then ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : ℚ) else 0 := by
      intro i
      have h := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E) (traceForm_nondegenerate ℚ E)
        (NumberField.integralBasis E) i j
      rw [Algebra.traceForm_apply, integralBasis_apply] at h
      rw [mul_right_comm, mul_comm, ← zsmul_eq_mul, map_zsmul]
      erw [h]
      split_ifs <;> simp
    simp [this]
  conv => enter [1]; rw [← (RingOfIntegers.basis E).sum_repr a]
  conv => enter [2]; rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [Finset.sum_smul, map_sum, smul_assoc, map_zsmul, Finset.mul_sum, mul_smul_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [hb]
  simp

theorem pairE_add (x y : X) : GlobalTheory.ArcQ.pairE (E := E) ξ (x + y) =
    GlobalTheory.ArcQ.pairE (E := E) ξ x + GlobalTheory.ArcQ.pairE (E := E) ξ y := by
  simp [GlobalTheory.ArcQ.pairE, smul_add, mul_add, Finset.sum_add_distrib]

theorem pairE_smul (a : 𝓞 E) (x : X) : GlobalTheory.ArcQ.pairE (E := E) ξ (a • x) =
    GlobalTheory.ArcQ.pairE (E := E) ξ x * a := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trace
  intro b
  rw [sub_mul, map_sub, trace_pairE, mul_assoc]
  have := trace_pairE ξ x (a * b)
  rw [← mul_smul, mul_comm b a, ← this]
  simp

theorem pairE_zsmul (a : ℤ) (x : X) : GlobalTheory.ArcQ.pairE (E := E) ξ (a • x) =
    a * GlobalTheory.ArcQ.pairE (E := E) ξ x := by
  have := pairE_smul (E := E) ξ (a : 𝓞 E) x
  rw [Int.cast_smul_eq_zsmul] at this
  rw [this]; simp [mul_comm]

theorem exists_mul_eq_int (b : 𝓞 E) (hb : b ≠ 0) : ∃ (c : 𝓞 E) (n : ℤ), n ≠ 0 ∧ c * b = n := by
  have h := Ideal.absNorm_mem (Ideal.span {b})
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨c, Ideal.absNorm (Ideal.span {b}), ?_, by simpa using hc⟩
  simpa [Ideal.absNorm_eq_zero_iff] using hb

theorem pairE_ne_zero [Module.Finite ℤ X] [Module.Free ℤ X] (hξ : ξ ≠ 0) (h1 : Module.finrank (𝓞 E) X = 1)
    (x : X) (hx : x ≠ 0) : GlobalTheory.ArcQ.pairE (E := E) ξ x ≠ 0 := by
  intro h0
  apply hξ
  have hz : ∀ a : 𝓞 E, ξ (a • x) = 0 := by
    intro a
    have := trace_pairE ξ x a
    rw [h0, zero_mul, map_zero] at this
    exact_mod_cast this.symm
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  ext y
  have hli : ¬ LinearIndependent (𝓞 E) ![x, y] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [h1] at this
  rw [LinearIndependent.pair_iff] at hli
  push Not at hli
  obtain ⟨a, b, hab, hne⟩ := hli
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := fun ha => hne ha hb
    obtain ⟨c, n, hn, hc⟩ := exists_mul_eq_int a ha
    rw [hb, zero_smul, add_zero] at hab
    have : n • x = 0 := by rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← hc, mul_smul, hab, smul_zero]
    exact hx ((smul_eq_zero.mp this).resolve_left hn)
  obtain ⟨c, n, hn, hc⟩ := exists_mul_eq_int b hb
  have : (c * a) • x + n • y = 0 := by
    rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← hc, mul_smul, mul_smul, ← smul_add, hab, smul_zero]
  have h2 := congrArg ξ this
  rw [map_add, hz, map_zsmul, map_zero, zero_add, smul_eq_mul] at h2
  simpa [hn] using h2

end Tr

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_mul' (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y
theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := map_add (IsCMField.complexConj E) x y
theorem cc_sub' (x y : E) : cc (x - y) = cc x - cc y := map_sub (IsCMField.complexConj E) x y
theorem cc_int (n : ℤ) : cc (n : E) = n := map_intCast (IsCMField.complexConj E) n
theorem cc_nat (n : ℕ) : cc (n : E) = n := map_natCast (IsCMField.complexConj E) n
theorem cc_two : cc (2 : E) = 2 := by simpa using cc_nat (E := E) 2
theorem cc_cc' (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = (starRingEnd ℂ) (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x
theorem trace_cc (x : E) : Algebra.trace ℚ E (cc x) = Algebra.trace ℚ E x :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
theorem cc_integral {x : E} (h : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  h.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
theorem im_zero {x : E} (h : cc x = x) (τ : E →+* ℂ) : (τ x).im = 0 := by
  have := emb_cc τ x
  rw [h] at this
  exact Complex.conj_eq_iff_im.mp this.symm

theorem exists_sym (a : 𝓞 E) : ∃ t : 𝓞 E, cc (t : E) = t ∧ ∀ μ : E, cc μ = μ →
    Algebra.trace ℚ E (μ * t) = 2 * Algebra.trace ℚ E (μ * a) := by
  refine ⟨⟨a + cc (a : E), a.2.add (cc_integral a.2)⟩, ?_, fun μ hμ => ?_⟩
  · change cc ((a : E) + cc (a : E)) = (a : E) + cc (a : E)
    rw [cc_add', cc_cc', add_comm]
  · change Algebra.trace ℚ E (μ * ((a : E) + cc (a : E))) = _
    rw [mul_add, map_add, ← trace_cc (μ * cc (a : E)), cc_mul', hμ, cc_cc']; ring

theorem exists_sep (S : Finset E) (hS : ∀ μ ∈ S, μ ≠ 0 ∧ cc μ = μ) :
    ∃ t : 𝓞 E, cc (t : E) = t ∧ ∀ μ ∈ S, Algebra.trace ℚ E (μ * t) ≠ 0 := by
  classical
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm
  let b := (RingOfIntegers.basis E).reindex e.symm
  let w : E → Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) → ℝ :=
    fun μ j => ((Algebra.trace ℚ E (μ * (b j : E)) : ℚ) : ℝ)
  have hw : ∀ (μ : E) (n : Fin _ → ℤ), ((Algebra.trace ℚ E (μ * ((∑ j, n j • b j : 𝓞 E) : E)) : ℚ) : ℝ) =
      ∑ j, w μ j * n j := by
    intro μ n
    have : ((∑ j, n j • b j : 𝓞 E) : E) = ∑ j, n j • (b j : E) := by simp
    rw [this, Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, map_zsmul]
    simp [w, mul_comm]
  obtain ⟨n, hn⟩ := ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_int_avoid (S.image w) (by
    intro z hz h0
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hz
    apply (hS μ hμ).1
    apply eq_zero_of_trace
    intro a
    have := hw μ (b.repr a)
    rw [b.sum_repr a, h0] at this
    simpa using this)
  obtain ⟨t, ht, ht'⟩ := exists_sym (∑ j, n j • b j)
  refine ⟨t, ht, fun μ hμ h => hn _ (Finset.mem_image_of_mem w hμ) ?_⟩
  rw [ht' μ (hS μ hμ).2] at h
  rw [← hw]
  have : Algebra.trace ℚ E (μ * ((∑ j, n j • b j : 𝓞 E) : E)) = 0 := by linarith
  rw [this]; simp

def Freq (ν : E) : Prop := cc ν = ν ∧ (∀ τ : E →+* ℂ, 0 ≤ (τ ν).re) ∧
  ∀ t : 𝓞 E, cc (t : E) = t → ∃ m : ℤ, Algebra.trace ℚ E (ν * t) = m

theorem slice_finite (J : ℚ) : {ν : E | Freq ν ∧ Algebra.trace ℚ E ν = J}.Finite := by
  obtain ⟨D, hD, h⟩ := exists_den (E := E)
  have hfin := Embeddings.finite_of_norm_le E ℂ (D * (2 * J))
  refine Set.Finite.of_finite_image (f := fun ν => (D : E) * (2 * ν)) (hfin.subset ?_) ?_
  · rintro _ ⟨ν, ⟨⟨h1, h2, h3⟩, hJ⟩, rfl⟩
    refine ⟨h _ fun a => ?_, fun φ => ?_⟩
    · obtain ⟨t, ht, ht'⟩ := exists_sym a
      obtain ⟨m, hm⟩ := h3 t ht
      refine ⟨m, ?_⟩
      rw [← hm, ht' ν h1, mul_assoc, two_mul, map_add, two_mul]
    · have e1 : ‖φ ν‖ = (φ ν).re := by
        rw [← Complex.abs_re_eq_norm.mpr (im_zero h1 φ), abs_of_nonneg (h2 φ)]
      have e2 : (φ ν).re ≤ J := by
        rw [← hJ, trace_re]
        exact Finset.single_le_sum (f := fun τ : E →+* ℂ => (τ ν).re) (fun τ _ => h2 τ) (Finset.mem_univ φ)
      simp only [map_mul, map_natCast, map_ofNat, norm_mul, Complex.norm_natCast, Complex.norm_ofNat, e1]
      gcongr
  · intro x _ y _ hxy
    have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
    simpa [hD'] using hxy

theorem int_eq_of_weighted_sum_eq_with_small_errors (M R A B : ℝ) (i j : ℤ) (hi : (0 : ℝ) ≤ i) (hj : (0 : ℝ) ≤ j) (hM : 0 ≤ M)
    (hR : M * (2 * j + 1) < R) (hA : |A| ≤ M * i) (hB : |B| ≤ M * j) (h : R * i + A = R * j + B) : i = j := by
  by_contra hij
  have hR0 : 0 ≤ R := le_trans (by positivity) hR.le
  have hdiff : R * ((i : ℝ) - j) = B - A := by linarith
  have habs : |R * ((i : ℝ) - j)| ≤ M * (i + j) := by
    rw [hdiff]
    calc |B - A| ≤ |B| + |A| := abs_sub _ _
      _ ≤ M * j + M * i := add_le_add hB hA
      _ = M * (i + j) := by ring
  have hne : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    have : (i - j : ℤ) ≠ 0 := sub_ne_zero.mpr hij
    have h := Int.one_le_abs this
    exact_mod_cast h
  have hkey : (i : ℝ) + j ≤ (2 * j + 1) * |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ j - i by linarith)
        (show (0 : ℝ) ≤ 2 * j + 1 by linarith)]
    · have h1 : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ i - j by linarith)
        (show (0 : ℝ) ≤ 2 * j by linarith)]
  rw [abs_mul, abs_of_nonneg hR0] at habs
  have : R * |(i : ℝ) - j| ≤ M * ((2 * j + 1) * |(i : ℝ) - j|) :=
    le_trans habs (mul_le_mul_of_nonneg_left hkey hM)
  nlinarith [abs_nonneg ((i : ℝ) - j)]

theorem exists_isolating (ν₀ : E) (h₀ : Freq ν₀) : ∃ u : 𝓞 E, cc (u : E) = u ∧ (∀ τ : E →+* ℂ, 0 < (τ u).re) ∧
    ∀ ν, Freq ν → Algebra.trace ℚ E (ν * u) = Algebra.trace ℚ E (ν₀ * u) → ν = ν₀ := by
  classical
  have hfin := slice_finite (E := E) (Algebra.trace ℚ E ν₀)
  obtain ⟨t, ht, hsep⟩ := exists_sep ((hfin.toFinset.filter (· ≠ ν₀)).image (· - ν₀)) (by
    intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hν
    exact ⟨sub_ne_zero.mpr hν.2, by rw [cc_sub', hν.1.1.1, h₀.1]⟩)
  set M : ℝ := ∑ τ : E →+* ℂ, |(τ t).re| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∀ τ : E →+* ℂ, |(τ t).re| ≤ M := fun τ =>
    Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  have hint : ∀ ν : E, Freq ν → ∃ i : ℤ, Algebra.trace ℚ E ν = i ∧ (0 : ℝ) ≤ i ∧
      |((Algebra.trace ℚ E (ν * t) : ℚ) : ℝ)| ≤ M * i := by
    intro ν hν
    obtain ⟨i, hi⟩ := hν.2.2 1 (by simpa using cc_nat (E := E) 1)
    have hi' : Algebra.trace ℚ E ν = i := by simpa using hi
    have hs : (i : ℝ) = ∑ τ : E →+* ℂ, (τ ν).re := by rw [← trace_re, hi']; simp
    refine ⟨i, hi', hs ▸ Finset.sum_nonneg fun τ _ => hν.2.1 τ, ?_⟩
    rw [trace_re, hs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    rw [map_mul, Complex.mul_re, im_zero hν.1, zero_mul, sub_zero, abs_mul, abs_of_nonneg (hν.2.1 τ), mul_comm]
    exact mul_le_mul_of_nonneg_right (hle τ) (hν.2.1 τ)
  obtain ⟨j, hj, hj0, hjb⟩ := hint ν₀ h₀
  obtain ⟨R, hR⟩ : ∃ R : ℕ, M * (2 * j + 1) < R := exists_nat_gt _
  have hu : (((R : 𝓞 E) + t : 𝓞 E) : E) = R + (t : E) := by simp
  have htr : ∀ ν : E, Algebra.trace ℚ E (ν * (R + (t : E))) = R * Algebra.trace ℚ E ν + Algebra.trace ℚ E (ν * t) := by
    intro ν
    rw [mul_add, map_add, mul_comm ν R, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  refine ⟨R + t, ?_, fun τ => ?_, fun ν hν h => ?_⟩
  · rw [hu, cc_add', cc_nat, ht]
  · rw [hu, map_add, map_natCast, Complex.add_re, Complex.natCast_re]
    have h1 := (abs_le.mp (hle τ)).1
    nlinarith [mul_nonneg hM0 hj0]
  · rw [hu, htr, htr] at h
    obtain ⟨i, hi, hi0, hib⟩ := hint ν hν
    have hij : i = j := by
      refine int_eq_of_weighted_sum_eq_with_small_errors M R _ _ i j hi0 hj0 hM0 hR hib hjb ?_
      rw [hi, hj] at h
      exact_mod_cast h
    by_contra hne
    have e : Algebra.trace ℚ E ν = Algebra.trace ℚ E ν₀ := by rw [hi, hj, hij]
    refine hsep (ν - ν₀) (Finset.mem_image_of_mem _ ?_) ?_
    · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hν, e⟩, hne⟩
    · rw [sub_mul, map_sub]; rw [e] at h; linarith

end CM

theorem exists_form_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] [Module.Free ℤ X] (ξ : Module.Dual ℤ X) (N : ℕ) (ν₀ : E), ξ ≠ 0 → Module.finrank (𝓞 E) X = 1 → 0 < N → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ∃ (be : LinearMap.BilinForm ℤ X) (s : E) (jj : ℤ), IsBePar ξ be s ∧ (∀ x y, be x y = be y x) ∧ (∀ x, x ≠ 0 → 0 < be x x) ∧ (∀ x y, (2 * N : ℤ) ∣ be x y) ∧ BetaAt ξ N be ν₀ jj := by
  intro E _ _ _ X _ _ _ _ ξ N ν₀ hξ h1 hN hc hpos hint
  obtain ⟨D, hD, hden⟩ := exists_den (E := E)
  set p : X → E := GlobalTheory.ArcQ.pairE (E := E) ξ with hp
  have hq : ∀ y, IsIntegral ℤ ((D : E) * cc (p y)) := by
    intro y
    have := cc_integral (hden (p y) fun a => ⟨_, trace_pairE ξ y a⟩)
    rwa [cc_mul', cc_nat] at this
  have hval : ∀ (t : 𝓞 E) (x y : X), ∃ m : ℤ,
      Algebra.trace ℚ E (2 * ((N * D : E) * t) * p x * cc (p y)) = 2 * N * m := by
    intro t x y
    refine ⟨ξ ((t * ⟨_, hq y⟩ : 𝓞 E) • x), ?_⟩
    rw [← trace_pairE]
    have : 2 * ((N * D : E) * t) * p x * cc (p y) = (2 * N : ℚ) • (p x * ((t : E) * (D * cc (p y)))) := by
      simp [Algebra.smul_def]; ring
    rw [this, map_smul, smul_eq_mul]
    rfl
  have hreal : ∀ t : 𝓞 E, cc (t : E) = t → cc ((N * D : E) * t) = (N * D : E) * t := by
    intro t ht
    rw [cc_mul', cc_mul', cc_nat, cc_nat, ht]
  have hlev : ∀ t : 𝓞 E, cc (t : E) = t → LevelPar ξ N ((N * D : E) * t) := by
    intro t ht
    refine ⟨hreal t ht, fun x y => ?_⟩
    obtain ⟨m, hm⟩ := hval t x y
    exact ⟨2 * m, by rw [hm]; push_cast; ring⟩
  have hfreq : ∀ ν : E, cc ν = ν → (∀ τ : E →+* ℂ, 0 ≤ (τ ν).re) →
      (∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν * s) = m) → Freq (ν * (N * D)) := by
    intro ν a b c
    refine ⟨by rw [cc_mul', cc_mul', cc_nat, cc_nat, a], fun τ => ?_, fun t ht => ?_⟩
    · have : (τ (ν * (N * D))).re = (τ ν).re * (N * D) := by simp
      rw [this]
      exact mul_nonneg (b τ) (by positivity)
    · rw [mul_assoc]; exact c _ (hlev t ht)
  obtain ⟨u, hu, hupos, huniq⟩ := exists_isolating _ (hfreq ν₀ hc hpos hint)
  set s : E := (N * D : E) * u with hs
  choose m hm using hval u
  let f : X → X → ℤ := fun x y => 2 * N * m x y
  have hf : ∀ x y, Algebra.trace ℚ E (2 * s * p x * cc (p y)) = (f x y : ℚ) := by
    intro x y; rw [hm]; simp [f]
  let be : LinearMap.BilinForm ℤ X := LinearMap.mk₂ ℤ f
    (fun x x' y => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, hp, pairE_add, ← map_add]; congr 1; ring)
    (fun n x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul n, ← hf, ← hf, hp, pairE_zsmul, ← zsmul_eq_mul (Algebra.trace ℚ E _) n, ← map_zsmul]
      congr 1; rw [zsmul_eq_mul]; ring)
    (fun x y y' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, hp, pairE_add, cc_add', ← map_add]; congr 1; ring)
    (fun n x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul n, ← hf, ← hf, hp, pairE_zsmul, cc_mul', cc_int,
        ← zsmul_eq_mul (Algebra.trace ℚ E _) n, ← map_zsmul]
      congr 1; rw [zsmul_eq_mul]; ring)
  have hbe : ∀ x y, be x y = f x y := fun _ _ => rfl
  obtain ⟨jj, hjj⟩ := hint s (hlev u hu)
  have hND : (0 : ℝ) < N * D := by positivity
  have hND' : (N * D : E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hN hD).ne'
  refine ⟨be, s, jj, ⟨hreal u hu, hf⟩, fun x y => ?_, fun x hx => ?_, fun x y => ⟨m x y, rfl⟩, hc, fun s' hs' => ?_⟩
  · apply Int.cast_injective (α := ℚ)
    rw [hbe, hbe, ← hf, ← hf, ← trace_cc, cc_mul', cc_mul', cc_mul', cc_cc', cc_two, hreal u hu]
    congr 1; ring
  · have : (0 : ℝ) < ((f x x : ℚ) : ℝ) := by
      rw [← hf, trace_re]
      refine Finset.sum_pos (fun τ _ => ?_) Finset.univ_nonempty
      have h0 : τ (p x) ≠ 0 := (map_ne_zero τ).mpr (pairE_ne_zero ξ hξ h1 x hx)
      have e : (τ (2 * s * p x * cc (p x))).re = 2 * ((N * D) * (τ u).re) * Complex.normSq (τ (p x)) := by
        rw [mul_assoc, map_mul, map_mul τ (p x), emb_cc, Complex.mul_conj, hs]
        simp [map_ofNat]
      rw [e]
      have := hupos τ
      have := Complex.normSq_pos.mpr h0
      positivity
    rw [hbe]
    exact_mod_cast this
  · have hss : s' = s := by
      obtain ⟨x, hx⟩ : ∃ x : X, x ≠ 0 := by
        by_contra hx
        push Not at hx
        exact hξ (by ext y; simp [hx y])
      have h0 : p x ≠ 0 := pairE_ne_zero ξ hξ h1 x hx
      have h0' : cc (p x) ≠ 0 := fun h => h0 (by rw [← cc_cc' (p x), h]; simpa using cc_nat (E := E) 0)
      have : 2 * (s' - s) * p x * cc (p x) = 0 := by
        apply eq_zero_of_trace
        intro a
        have e1 := hs'.2 (a • x) x
        have e2 := hf (a • x) x
        rw [hbe, ← e2, ← sub_eq_zero, ← map_sub] at e1
        rw [← e1, hp, pairE_smul]
        congr 1; ring
      simpa [h0, h0', sub_eq_zero] using this
    subst hss
    refine ⟨hjj, fun ν a b c d => ?_⟩
    have := huniq _ (hfreq ν a b c) (by rw [mul_assoc ν, mul_assoc ν₀, d, hjj])
    exact mul_right_cancel₀ hND' this

end GlobalTheory.ArcQ.Isolate
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.AnAtFrame

open GlobalTheory.ArcFlow ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Transfer

variable {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]

omit [IsCMField E] in

lemma pairE_comp (e : X →ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y) (ξ₁ : Module.Dual ℤ X) (h : ∀ x, ξ₁ x = ξ (e x)) (x : X) :
    pairE (E := E) ξ₁ x = pairE ξ (e x) := by
  simp only [pairE, h, map_smul]

lemma betaAt_comp (e : X ≃ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y) (ξ₁ : Module.Dual ℤ X) (h : ∀ x, ξ₁ x = ξ (e x))
    (be : LinearMap.BilinForm ℤ Y) (be₁ : LinearMap.BilinForm ℤ X) (hbe : ∀ x x', be₁ x x' = be (e x) (e x'))
    {N : ℕ} {ν₀ : E} {jj : ℤ} (hb : BetaAt ξ N be ν₀ jj) : BetaAt ξ₁ N be₁ ν₀ jj := by
  have hp : ∀ x, pairE (E := E) ξ₁ x = pairE ξ (e x) := pairE_comp e.toLinearMap ξ ξ₁ h
  refine ⟨hb.1, fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hb.2 s ⟨hs.1, fun y y' => by
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective y'
    rw [← hp, ← hp, hs.2, hbe]⟩
  refine ⟨h1, fun ν hν hν' hl => h2 ν hν hν' fun s' hs' => hl s' ⟨hs'.1, fun x x' => ?_⟩⟩
  rw [hp, hp]
  exact hs'.2 _ _

lemma adj_of_isBePar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (ξ : Module.Dual ℤ Y) (be : LinearMap.BilinForm ℤ Y) {s : E}
    (hs : IsBePar ξ be s) (a : 𝓞 E) (x x' : Y) : be (a • x) x' = be x (H.bar a • x') := by
  obtain ⟨p1, -⟩ := pairE_properties E Y ξ
  have h : (be (a • x) x' : ℚ) = be x (H.bar a • x') := by
    rw [← hs.2, ← hs.2, p1, p1, HermitianTraceFormVanishing.cc_mul, H.bar_eq]
    have : cc (IsCMField.complexConj E (a : E)) = a := by simp [FD.cc]
    rw [this]
    congr 1; ring
  exact_mod_cast h

end Transfer

variable {r : ℕ} (X : Data E r)

lemma transv_of_levelPar {La Y : Type} [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Y] [Module (𝓞 E) Y]
    (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
    (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (y : La →ₗ[𝓞 E] Y) (hκ : X.κ0 = 2 * X.ξ0) (hrep : ∀ θ : Module.Dual ℤ Y, ∃ t, ∀ v, -EF t v = θ (y v))
    (ξ : Module.Dual ℤ Y) (t : La) (ht : ∀ v, -EF t v = ξ (y v)) {N : ℕ} (hN : 0 < N) (s : E)
    (hs : LevelPar ξ N s) : ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
      (transvMat X.Gm (φ t : Fin r → E) (s * X.κ0)).mulVec v - v = (N : E) • u := by
  obtain ⟨p1, p2, p3, -⟩ := pairE_properties E Y ξ
  have hp := pairE_eq X φ EF iso y t ξ ht
  have hc0 := X.ξ0_im
  have hcj := herm_conj X.Gm X.Gm_herm
  have hΛ : ∀ w ∈ X.Λ, ∃ v, (φ v : Fin r → E) = w := fun w hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩
  set ξ' : Fin r → E := (φ t).1 with hξ'
  have htr : ∀ (s : E) v v', Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ (y v'))) =
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm ((s * X.κ0 * herm X.Gm (φ v : Fin r → E) ξ') • ξ') (φ v')) := by
    intro s v v'
    rw [hp, hp, HermitianTraceFormVanishing.cc_mul, cc_neg, hc0, hcj, herm_smul_left, hκ]
    congr 1; ring
  intro w hw
  obtain ⟨v, rfl⟩ := hΛ w hw
  obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual ℤ Y, ∀ x,
      Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ x)) = (N : ℚ) * θ x := by
    choose m hm using hs.2 (y v)
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨(AddMonoidHom.mk' m fun a b => ?_).toIntLinearMap, hm⟩
    have e := hm (a + b)
    rw [p2, cc_add, mul_add, map_add, hm, hm, ← mul_add] at e
    exact_mod_cast (mul_left_cancel₀ hN' e).symm
  obtain ⟨t', ht'⟩ := hrep θ
  refine ⟨-(φ t' : Fin r → E), X.Λ.neg_mem (φ t').2, ?_⟩
  rw [transvMat_mulVec, ← sub_eq_zero]
  refine eq_zero_of_trace_lattice X _ fun w hw => ?_
  obtain ⟨v', rfl⟩ := hΛ w hw
  have e := hθ (y v')
  rw [htr, ← ht', Int.cast_neg, iso, ← map_neg, ← nsmul_eq_mul, ← map_nsmul, ← sub_eq_zero, ← map_sub] at e
  rw [← neg_eq_zero, ← map_neg, ← e, herm_sub_left, smul_neg, ← neg_smul, herm_smul_left X.Gm (-(N : E))]
  congr 1; rw [nsmul_eq_mul]; ring

lemma re_eq_of_maj {x : Frame X.Ψ r} (hx : x ∈ X.dom) {La : Type} [AddCommGroup La] (φ : La →+ (Fin r → E)) {g : ℕ}
    (P : La →+ (Fin g → ℂ)) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (h : ∀ v, (hermForm Hm (P v) (P v)).re = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 (φ v))) (v w : La) :
    (hermForm Hm (P v) (P w)).re = ∑ τ, X.c τ * (X.Hf x τ (Data.emb τ.1 (φ v)) (Data.emb τ.1 (φ w))).re := by
  have hm : ∀ τ u, X.maj x τ u = (X.Hf x τ u u).re := fun τ u => by rw [X.Hf_self hx]; simp
  have he : ∀ τ : X.Ψ, Data.emb τ.1 (φ (v + w)) = Data.emb τ.1 (φ v) + Data.emb τ.1 (φ w) := fun τ => by
    funext k; simp [Data.emb]
  have hs : ∀ τ u u', (X.Hf x τ u' u).re = (X.Hf x τ u u').re := fun τ u u' => by
    rw [← UnipotentCoefficientShift.Hf_conj hx, Complex.conj_re]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  have h4 : (hermForm Hm (P w) (P v)).re = (hermForm Hm (P v) (P w)).re := by
    rw [← OfPeriod.sesq_apply, ← OfPeriod.sesq_conj hH, Complex.conj_re, OfPeriod.sesq_apply]
  simp only [hm] at h1 h2 h3
  simp only [he, UnipotentCoefficientShift.Hf_add_left, UnipotentCoefficientShift.Hf_add_right, Complex.add_re, hs _ (Data.emb _ (φ v)), mul_add,
    Finset.sum_add_distrib] at h1
  rw [← OfPeriod.sesq_apply, map_add P] at h1
  simp only [map_add, LinearMap.add_apply, Complex.add_re, OfPeriod.sesq_apply] at h1
  linarith

lemma Hf_eq_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ≠ 0) (m : Fin r → E) (n : ℕ) (e e' : E)
    (h : (n : ℂ) • X.aproj x ξ (X.embV m) = X.embV (e • ξ)) (τ : X.Ψ) :
    X.Hf x τ (Data.emb τ.1 ((n : ℤ) • m - e • ξ)) (Data.emb τ.1 (e' • ξ)) = 0 := by
  have h0 : Data.emb τ.1 ξ ≠ 0 := fun h0 => hξ (funext fun k => by simpa [Data.emb] using congrFun h0 k)
  have hs : ∀ a : E, Data.emb τ.1 (a • ξ) = τ.1 a • Data.emb τ.1 ξ := fun a => by funext k; simp [Data.emb]
  have h1 : Data.emb τ.1 ((n : ℤ) • m - e • ξ) = (n : ℂ) • Data.emb τ.1 m - τ.1 e • Data.emb τ.1 ξ := by
    funext k; simp [Data.emb]
  have h2 : X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ h0).ne'
  have h3 := congrFun h τ
  simp only [Pi.smul_apply, Data.aproj, Data.lineV, Data.embV, hs, smul_smul] at h3
  have h4 := smul_left_injective ℂ h0 h3
  rw [h1, hs, UnipotentCoefficientShift.Hf_smul_right, UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, UnipotentCoefficientShift.Hf_smul_left, ← h4]
  field_simp
  simp

lemma exists_quot {La : Type} [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La]
    (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
    (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (t : La) (ht : (φ t : Fin r → E) ≠ 0) :
    ∃ (Y : Submodule (𝓞 E) E) (y : La →ₗ[𝓞 E] Y) (ξ : Module.Dual ℤ Y), Function.Surjective y ∧
      Module.Finite ℤ Y ∧ Module.Free ℤ Y ∧ Module.finrank (𝓞 E) Y = 1 ∧ ξ ≠ 0 ∧ (∀ v, -EF t v = ξ (y v)) ∧
      (∀ v, y v = 0 ↔ herm X.Gm (φ v : Fin r → E) (φ t) = 0) ∧
      ∀ v, y v = 0 ↔ ∀ t', (∃ e : E, (φ t' : Fin r → E) = e • (φ t : Fin r → E)) → EF t' v = 0 := by
  have hsm : ∀ (β : 𝓞 E) v, (φ (β • v) : Fin r → E) = (β : E) • (φ v : Fin r → E) := fun β v => by
    rw [map_smul]; rfl
  have hcj := herm_conj X.Gm X.Gm_herm
  let f : La →ₗ[𝓞 E] E :=
    { toFun := fun v => herm X.Gm (φ v : Fin r → E) (φ t)
      map_add' := fun v v' => by rw [map_add, Submodule.coe_add, herm_add_left]
      map_smul' := fun a v => by rw [hsm, herm_smul_left]; rfl }
  have hf0 : ∀ v, f.rangeRestrict v = 0 ↔ herm X.Gm (φ v : Fin r → E) (φ t) = 0 := fun v => Subtype.ext_iff
  have hk : ∀ v, f.rangeRestrict v = 0 ↔
      ∀ t', (∃ e : E, (φ t' : Fin r → E) = e • (φ t : Fin r → E)) → EF t' v = 0 := fun v => by
    rw [hf0]
    refine ⟨fun h t' ⟨e, he⟩ => ?_, fun h => ?_⟩
    · have := iso t' v
      rw [he, herm_smul_left, ← hcj, h] at this
      simpa using this
    · have : -X.ξ0 * herm X.Gm (φ t : Fin r → E) (φ v) = 0 := eq_zero_of_trace_mul _ fun β => by
        have h1 := iso (β • t) v
        rw [h _ ⟨β, hsm β t⟩, hsm, herm_smul_left] at h1
        rw [mul_left_comm, ← h1, Int.cast_zero]
      rw [← hcj, (mul_eq_zero.1 this).resolve_left (neg_ne_zero.2 X.ξ0_ne)]
      simp
  have hy := f.surjective_rangeRestrict
  haveI : Module.Finite ℤ (LinearMap.range f) := Module.Finite.trans (𝓞 E) _
  have hle : f.rangeRestrict.toAddMonoidHom.ker ≤ (-EF t).toAddMonoidHom.ker := fun v hv => by
    simpa using (hk v).1 hv t ⟨1, (one_smul _ _).symm⟩
  let ξ : LinearMap.range f →+ ℤ := f.rangeRestrict.toAddMonoidHom.liftOfSurjective hy ⟨_, hle⟩
  have hξ : ∀ v, -EF t v = ξ.toIntLinearMap (f.rangeRestrict v) := fun v =>
    (AddMonoidHom.liftOfRightInverse_comp_apply f.rangeRestrict.toAddMonoidHom _ (Function.rightInverse_surjInv hy)
      ⟨_, hle⟩ v).symm
  have hξ0 : ξ.toIntLinearMap ≠ 0 := fun h => ht (eq_zero_of_trace_lattice X _ fun w hw => by
    have h1 := hξ (φ.symm ⟨w, hw⟩)
    have h2 := iso t (φ.symm ⟨w, hw⟩)
    rw [h, LinearMap.zero_apply, neg_eq_zero] at h1
    rw [h1, neg_mul, map_neg] at h2
    simpa using h2.symm)
  refine ⟨LinearMap.range f, f.rangeRestrict, ξ.toIntLinearMap, hy, inferInstance, inferInstance, ?_, hξ0, hξ, hf0, hk⟩
  haveI : Nontrivial (LinearMap.range f) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hξ0 (LinearMap.ext fun a => by rw [Subsingleton.elim a 0]; simp)
  have h2 : Module.rank (𝓞 E) (LinearMap.range f) ≤ 1 := by
    refine (Submodule.rank_le _).trans ?_
    rw [← IsFractionRing.rank_right_eq (𝓞 E) E E, Module.rank_self]
  exact le_antisymm (Module.finrank_le_of_rank_le (by simpa using h2)) Module.finrank_pos

theorem exists_anArc_onOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  intro E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x n' ν₀ hσ hU hξ' hx hn hν hν' hint
  letI := H.starRing
  obtain ⟨t, rfl⟩ : ∃ t, (Uw.φ k t : Fin r → E) = ξ' := ⟨(Uw.φ k).symm ⟨ξ', hξ'.1⟩, by simp⟩
  have hfin := (Uw.F.Di (Uw.ik k)).fin
  have hP := Uw.period k ⟨x, hx⟩
  obtain ⟨Hm, hHm⟩ := hP.2.2.2.2
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => by
    subst h
    exact hξ'.2.2 (Subsingleton.elim _ _)
  obtain ⟨hmaj, hκ, -⟩ := GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k ⟨x, hx⟩ Hm hσ hU hHm
  replace hκ := hκ hr
  obtain ⟨Y, y, ξ, hy, _, _, hY, hξ, ht, hy0, hker⟩ := exists_quot (U.X k) (Uw.φ k) _ (Uw.iso k) t hξ'.2.2
  have hrep : ∀ (Z : Type) [AddCommGroup Z] [Module (𝓞 E) Z] (z : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] Z)
      (θ : Module.Dual ℤ Z), ∃ t, ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = θ (z v) := fun Z _ _ z θ => by
    obtain ⟨t, ht⟩ := (Uw.F.Di (Uw.ik k)).unimod.2 (-(θ ∘ₗ z.toAddMonoidHom.toIntLinearMap))
    exact ⟨t, fun v => by rw [ht]; simp⟩
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨be, s, jj, hs, hsym, hpos, hdvd, hbeta⟩ := GlobalTheory.ArcQ.Isolate.exists_form_isolating E Y ξ l.M' ν₀ hξ hY hM hν hν'
    fun s hs => hint s hs.1 (transv_of_levelPar (U.X k) (Uw.φ k) _ (Uw.iso k) y hκ (hrep Y y) ξ t ht hM s hs)
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  let Hh : Submodule (𝓞 E) (Uw.F.Di (Uw.ik k)).La :=
    ((Submodule.span E {(Uw.φ k t : Fin r → E)}).restrictScalars (𝓞 E)).comap φ
  have hHh : ∀ v, v ∈ Hh ↔ ∃ e : E, (Uw.φ k v : Fin r → E) = e • (Uw.φ k t : Fin r → E) := fun v =>
    Submodule.mem_span_singleton.trans (exists_congr fun _ => eq_comm)
  have hker' : ∀ v, y v = 0 ↔ ∀ t' ∈ Hh, (Uw.F.Di (Uw.ik k)).EF t' v = 0 := fun v => by
    simp only [hHh, hker]
  have hyH : ∀ v ∈ Hh, y v = 0 := fun v hv => by
    obtain ⟨e, he⟩ := (hHh v).1 hv
    rw [hy0, he, herm_smul_left, hξ'.2.1, mul_zero]
  obtain ⟨A, e, gam, h, hbe, hchi, hpsi, hEF, hgy, -, hact, hh, -, -, -, -, -, -, huniq, hct, hrk, tyB, hF, hD⟩ :=
    GlobalTheory.OfPeriod.exists_anArc_of_period (Uw.F.Di (Uw.ik k)) hP hHm.2.2 Hh
      (fun m v hm hv => by
        obtain ⟨e, he⟩ := (hHh _).1 hv
        refine (hHh v).2 ⟨(m : E)⁻¹ * e, ?_⟩
        have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
        rw [mul_smul, ← he, map_zsmul, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul E, inv_smul_smul₀ hm'])
      (fun v hv v' hv' => (hker' v').1 (hyH v' hv') v hv) y hy hker' be hsym hpos
      (adj_of_isBePar H ξ be hs) (fun a => (dvd_mul_right _ _).trans (hdvd a a))
  have hX : Module.finrank (𝓞 E) A.X = 1 := e.finrank_eq.trans hY
  rw [hX] at hrk
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  rw [← hrk, hp, hq] at hD
  obtain ⟨-, -, htyB, DB, eB, hp', hq', hB1, hB2, hB3⟩ := hD ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ Uw.e)
  let ξ₁ : Module.Dual ℤ A.X := ξ ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap
  have hξ₁ : ∀ a, ξ₁ a = ξ (e a) := fun _ => rfl
  have hξ₁0 : ξ₁ ≠ 0 := fun h0 => hξ (LinearMap.ext fun a => by
    rw [← e.apply_symm_apply a, ← hξ₁, h0]; rfl)
  have ht₁ : ∀ v, -(Uw.F.Di (Uw.ik k)).EF t v = ξ₁ (gam v).y := fun v => by rw [hξ₁, hgy, ht]
  refine ⟨A, gam, ξ₁, jj, DB, tyB, eB, ⟨hEF, ⟨t, rfl, ht₁⟩, ?_⟩, hξ₁0, hX, fun a a' => by rw [hbe]; exact hdvd _ _,
    betaAt_comp e ξ ξ₁ hξ₁ be A.be hbe hbeta, ⟨hchi, hpsi⟩, fun a => ?_,
    ⟨hF, by rw [hp', hq']; exact htyB, hB1, hB2, hB3⟩, hp', hq'⟩
  · let nn := gam.symm.toLinearMap ∘ₗ A.nn ∘ₗ gam.toLinearMap
    have hnn : ∀ v, gam (nn v) = A.nn (gam v) := fun v => gam.apply_symm_apply _
    obtain ⟨sE, -, hsE, -, -, hform⟩ := rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) (A.yLin ∘ₗ gam.toLinearMap) hX hκ
      (A.yLin_surjective.comp gam.surjective) A.be A.be_symm A.be_pos nn
      (fun v v' => by rw [← hEF, hnn, A.nn_apply, A.EF_n_left, neg_neg]; rfl) (hrep _ _) ξ₁ hξ₁0 t ht₁
      (e.injective (by rw [map_zero]; exact (hgy t).trans (hyH t ((hHh t).2 ⟨1, (one_smul _ _).symm⟩))))
    obtain ⟨T₀, hT₀⟩ := A.exists_BwMat_posDef
    refine ⟨T₀, fun w hw => ?_⟩
    let P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ) :=
      h.symm.toLinearMap.toAddMonoidHom.comp ((A.Pw w).comp gam.toLinearMap.toAddMonoidHom)
    have hPe : ∀ v, P v = h.symm (A.Pw w (gam v)) := fun _ => rfl
    have hPw := A.isPeriod (hT₀ w hw) (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) h.symm
      (fun a v i => by
        have := hact a (h.symm v)
        rw [h.apply_symm_apply] at this
        rw [← this, h.symm_apply_apply]) gam.toAddEquiv gam.map_smul hEF P hPe
    obtain ⟨hs, hPm⟩ := flow_period Uw hσ hU k hκ nn _ hξ'.2.1 sE hsE.1 hform ⟨x, hx⟩ w P hPw fun v => by
      rw [hPe, h.symm_apply_eq, map_add, map_smul, hh, hh, hnn, A.degeneratingTori_basePeriodMap_nilpotentMap, A.Pw_apply]
    exact ⟨_, hs, h, fun v => by rw [hPm, hPe, h.apply_symm_apply]⟩
  · rw [← natCast_zsmul]
    refine hct n' (fun v hv a ha ha' => ?_) a
    obtain ⟨e₀, he₀, hproj⟩ := hn (Uw.φ k v) ⟨(Uw.φ k v).2, (hy0 v).1 hv⟩
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, (Uw.φ k t₀ : Fin r → E) = e₀ • (Uw.φ k t : Fin r → E) :=
      ⟨(Uw.φ k).symm ⟨_, he₀⟩, by simp⟩
    have ht₀' := (hHh t₀).2 ⟨e₀, ht₀⟩
    refine ⟨t₀, ht₀', (huniq ((n' : ℤ) • v) (by rw [map_zsmul, hv, smul_zero])).unique
      ⟨Submodule.subset_span ⟨t₀, ht₀', rfl⟩, fun t' ht' => ?_⟩ ⟨zsmul_mem ha _, fun t' ht' => ?_⟩⟩
    · rw [← map_sub]
      refine Complex.ext ?_ ?_
      · obtain ⟨e', he'⟩ := (hHh t').1 ht'
        rw [re_eq_of_maj (U.X k) hx φ.toAddMonoidHom _ hHm.1 hmaj]
        refine Finset.sum_eq_zero fun τ _ => ?_
        have h1 : φ.toAddMonoidHom ((n' : ℤ) • v - t₀) =
            (n' : ℤ) • (Uw.φ k v : Fin r → E) - e₀ • (Uw.φ k t : Fin r → E) := by
          rw [map_sub, map_zsmul, ← ht₀]; rfl
        rw [h1, show φ.toAddMonoidHom t' = _ from he', Hf_eq_zero (U.X k) hx hξ'.2.2 _ n' e₀ e' hproj]
        simp
      · have halt : (Uw.F.Di (Uw.ik k)).EF.IsAlt := (Uw.F.Di (Uw.ik k)).alt
        rw [hHm.2.2, halt.eq_iff.1 ((hker' _).1 (by rw [map_sub, map_zsmul, hv, hyH t₀ ht₀']; simp) t' ht')]
        simp
    · rw [map_zsmul, ← smul_sub, ← OfPeriod.sesq_apply, map_zsmul, LinearMap.smul_apply, OfPeriod.sesq_apply,
        ha' t' ht', smul_zero]

end GlobalTheory.AnAtFrame
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  atlas_forward_decl GlobalTheory.AnAtFrame.exists_anArc_onOrbit
end
