import ReciprocityTheory.Chebotarev.EulerSum
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK
import Mathlib
import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical

namespace AdmissibleUnits

variable {K : Type} [Field K] [NumberField K]

lemma indep (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (a b : ℚ)
    (h : (a : K) + (b : K) * x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨?_, rfl⟩
    simpa using h
  · exfalso
    have hxq : x = ((-a / b : ℚ) : K) := by
      have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
      push_cast
      field_simp
      linear_combination h
    rw [hxq] at hx
    have h2 : ((-a / b) ^ 2 : ℚ) = -(d : ℚ) := by exact_mod_cast hx
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (-a / b)]

lemma span (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (y : K) : ∃ a b : ℚ, y = (a : K) + (b : K) * x := by
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply indep d hd x hx s t
    simpa [Algebra.smul_def, eq_ratCast] using hst
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have := B.sum_repr y
  rw [Fin.sum_univ_two] at this
  simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one] at this
  conv_lhs => rw [← this]
  simp [Algebra.smul_def, eq_ratCast, B]

end AdmissibleUnits

namespace AdmissibleUnits

variable {K : Type} [Field K] [NumberField K]

lemma conj_ne (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (φ : K →+* ℂ) :
    starRingEnd ℂ (φ x) ≠ φ x := by
  intro h
  rw [Complex.conj_eq_iff_re] at h
  have h2 : (φ x) ^ 2 = -(d : ℂ) := by simpa using congrArg φ hx
  rw [← h] at h2
  have h3 : ((φ x).re ^ 2 : ℝ) = -(d : ℝ) := by exact_mod_cast h2
  have : (0 : ℝ) < d := by exact_mod_cast hd
  nlinarith [sq_nonneg (φ x).re]

lemma norm_eq (d : ℕ) (hd : 0 < d) (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (α : K) : ((Algebra.norm ℚ α : ℚ) : ℝ) = ‖φ α‖ ^ 2 := by
  set ψ : K →ₐ[ℚ] ℂ := φ.toRatAlgHom
  set ψ' : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp φ).toRatAlgHom
  have hne : ψ ≠ ψ' := by
    intro h
    have := congrArg (fun f : K →ₐ[ℚ] ℂ => f x) h
    simp only [ψ, ψ', RingHom.toRatAlgHom_apply, RingHom.comp_apply] at this
    exact conj_ne d hd x hx φ this.symm
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by rw [AlgHom.card, hK]
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {ψ, ψ'} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ α
  rw [huniv, Finset.prod_pair hne] at h
  simp only [ψ, ψ', RingHom.toRatAlgHom_apply, RingHom.comp_apply] at h
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h' : (((Algebra.norm ℚ α : ℚ) : ℝ) : ℂ) = ((‖φ α‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h]; simp
  exact_mod_cast h'

end AdmissibleUnits

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Polynomial Matrix Classical
open scoped Pointwise

lemma squarefree_neg_natCast_prime (d : ℕ) [Fact d.Prime] : Squarefree (-(d : ℤ)) := by
  have hp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  exact hp.neg.squarefree

lemma covA_adjoin (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime]
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    IntermediateField.adjoin ℚ {x} = ⊤ := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hnot : x ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, rfl⟩
    have h2 : q ^ 2 = -(d : ℚ) := (algebraMap ℚ K).injective (by simpa using hx)
    have hd : (0 : ℚ) < d := by exact_mod_cast (Fact.out : d.Prime).pos
    nlinarith [sq_nonneg q]
  have hle : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
  have hne : (minpoly ℚ x).natDegree ≠ 1 := fun h => hnot (minpoly.natDegree_eq_one_iff.mp h)
  have hpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have hfin : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    omega
  exact IntermediateField.eq_of_le_of_finrank_le le_top
    (by rw [IntermediateField.finrank_top', hK, hfin])

lemma covA_discr (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    NumberField.discr K = -(d : ℤ) := by
  refine Formalism.HF.P.quadDiscr_ne_one K (-(d : ℤ)) x (by push_cast; exact hx)
    (covA_adjoin K d x hx hK) (squarefree_neg_natCast_prime d) ?_ ?_
  · omega
  · have := (Fact.out : d.Prime).pos
    omega

lemma covA_sq_im (s : ℂ) (d : ℕ) (hd : 0 < d) (hs : s ^ 2 = -(d : ℂ)) :
    s.im ^ 2 = (d : ℝ) := by
  have h1 := congrArg Complex.re hs
  have h2 := congrArg Complex.im hs
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : s.re = 0 := by
    rcases mul_eq_zero.mp (show s.re * s.im = 0 by linarith) with h | h
    · exact h
    · rw [h] at h1
      nlinarith [sq_nonneg s.re]
  rw [hre] at h1
  nlinarith

lemma covA_span (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    ∃ ω : 𝓞 K, (ω : K) = (1 + x) / 2 ∧
      ∀ y : 𝓞 K, ∃ m n : ℤ, y = (m : 𝓞 K) + (n : 𝓞 K) * ω := by
  have hd : d.Prime := Fact.out
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd.pos
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d = 4 * k + 3 := ⟨d / 4, by omega⟩
  have hxr : ∀ q : ℚ, (q : K) ≠ x := by
    intro q hq
    have h2 : ((q ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K) := by
      push_cast
      rw [hq, hx]
    have h3 : q ^ 2 = -(d : ℚ) := Rat.cast_injective h2
    nlinarith [sq_nonneg q]
  have hωint : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((k : ℤ) + 1), by monicity!, ?_⟩
    have hx' : x ^ 2 = -(4 * (k : K) + 3) := by
      rw [hx, hk]
      push_cast
      ring
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    push_cast
    linear_combination (1 / 4 : K) * hx'
  refine ⟨⟨(1 + x) / 2, hωint⟩, rfl, ?_⟩
  intro y
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hxr (-(s / t))
      have htK : (t : K) ≠ 0 := by exact_mod_cast ht
      rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
      push_cast
      rw [neg_eq_iff_eq_neg, div_eq_iff htK]
      linear_combination hst
  obtain ⟨a, b, hab⟩ : ∃ a b : ℚ, (y : K) = (a : K) + (b : K) * x := by
    set bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK]) with hbs
    refine ⟨bs.repr y 0, bs.repr y 1, ?_⟩
    conv_lhs => rw [← bs.sum_repr (y : K)]
    simp [Fin.sum_univ_two, hbs, coe_basisOfLinearIndependentOfCardEqFinrank, Rat.smul_def]
  have hyint : IsIntegral ℤ (y : K) := RingOfIntegers.isIntegral_coe y
  obtain ⟨A, hA, N, hN⟩ : ∃ A : ℤ, (A : ℚ) = 2 * a ∧ ∃ N : ℤ, (N : ℚ) = a ^ 2 + d * b ^ 2 := by
    by_cases hb : b = 0
    · subst hb
      have h1 : (y : K) = algebraMap ℚ K a := by
        rw [hab]
        simp
      have h2 : IsIntegral ℤ a := by
        rw [← isIntegral_algebraMap_iff (algebraMap ℚ K).injective, ← h1]
        exact hyint
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
      refine ⟨2 * z, by simp [← hz], z ^ 2, by simp [← hz]⟩
    · set q : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (2 * a) * Polynomial.X +
        Polynomial.C (a ^ 2 + d * b ^ 2) with hq
      have hqm : q.Monic := by
        rw [hq]
        monicity!
      have hqd : q.natDegree = 2 := by
        rw [hq]
        compute_degree!
      have hqy : Polynomial.aeval (y : K) q = 0 := by
        rw [hq]
        simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
          eq_ratCast]
        rw [hab]
        push_cast
        linear_combination (b : K) ^ 2 * hx
      have hnr : (y : K) ∉ (algebraMap ℚ K).range := by
        rintro ⟨r, hr⟩
        apply hxr ((r - a) / b)
        have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
        rw [eq_ratCast] at hr
        push_cast
        rw [div_eq_iff hbK, hr, hab]
        ring
      have hmin : q = minpoly ℚ (y : K) := by
        refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic
          (Algebra.IsIntegral.isIntegral _)) hqm (minpoly.dvd ℚ _ hqy) ?_
        have h1 : (minpoly ℚ (y : K)).natDegree ≠ 1 := fun h =>
          hnr (minpoly.natDegree_eq_one_iff.mp h)
        have h0 : 0 < (minpoly ℚ (y : K)).natDegree :=
          minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral _)
        omega
      have hZ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hyint
      have c1 := congrArg (fun p => Polynomial.coeff p 1) (hmin.trans hZ)
      have c0 := congrArg (fun p => Polynomial.coeff p 0) (hmin.trans hZ)
      simp only [hq, Polynomial.coeff_map, Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
        eq_intCast] at c1 c0
      refine ⟨-(minpoly ℤ (y : K)).coeff 1, ?_, (minpoly ℤ (y : K)).coeff 0, ?_⟩
      · push_cast
        rw [← c1]
        norm_num
      · rw [← c0]
        norm_num
  have sqint : ∀ r : ℚ, ∀ M : ℤ, (d : ℚ) * r ^ 2 = M → ∃ B : ℤ, (B : ℚ) = r := by
    intro r M hr
    have hden : r.den = 1 := by
      have e : (d : ℚ) * (r.num : ℚ) ^ 2 = M * (r.den : ℚ) ^ 2 := by
        have h := hr
        rw [← Rat.num_div_den r, div_pow, mul_div_assoc', div_eq_iff (by positivity)] at h
        exact h
      have e' : (d : ℤ) * r.num ^ 2 = M * (r.den : ℤ) ^ 2 := by exact_mod_cast e
      have hcop : IsCoprime ((r.den : ℤ) ^ 2) (r.num ^ 2) := by
        have h0 : IsCoprime (r.den : ℤ) r.num := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          exact r.reduced.symm
        exact h0.pow
      have hdvd : ((r.den : ℤ) ^ 2) ∣ (d : ℤ) := by
        have h1 : ((r.den : ℤ) ^ 2) ∣ (d : ℤ) * r.num ^ 2 := ⟨M, by rw [e']; ring⟩
        exact hcop.dvd_of_dvd_mul_right h1
      have h2 : r.den ^ 2 ∣ d := by exact_mod_cast hdvd
      have h3 : r.den ∣ d := (dvd_pow_self _ two_ne_zero).trans h2
      rcases (Nat.dvd_prime hd).mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at h2
        have h4 := Nat.le_of_dvd hd.pos h2
        nlinarith [hd.two_le]
    exact ⟨r.num, Rat.coe_int_num_of_den_eq_one hden⟩
  obtain ⟨B, hB⟩ := sqint (2 * b) (4 * N - A ^ 2) (by push_cast; rw [hN, hA]; ring)
  have e4 : 4 * N = A ^ 2 + (4 * (k : ℤ) + 3) * B ^ 2 := by
    have : (4 * N : ℚ) = A ^ 2 + d * B ^ 2 := by
      rw [hN, hA, hB]
      ring
    have h' : (4 * N : ℤ) = A ^ 2 + d * B ^ 2 := by exact_mod_cast this
    rw [h', hk]
    push_cast
    ring
  obtain ⟨m, hm⟩ : ∃ m : ℤ, A - B = 2 * m := by
    rcases Int.even_or_odd A with ⟨u, hu⟩ | ⟨u, hu⟩ <;>
      rcases Int.even_or_odd B with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨u - v, by rw [hu, hv]; ring⟩
    · exfalso
      rw [hu, hv] at e4
      have h5 : 4 * (N - u ^ 2 - (4 * k + 3) * (v ^ 2 + v) - k) = 3 := by linear_combination e4
      generalize N - u ^ 2 - (4 * k + 3) * (v ^ 2 + v) - k = X at h5
      omega
    · exfalso
      rw [hu, hv] at e4
      have h5 : 4 * (N - u ^ 2 - u - (4 * k + 3) * v ^ 2) = 1 := by linear_combination e4
      generalize N - u ^ 2 - u - (4 * k + 3) * v ^ 2 = X at h5
      omega
    · exact ⟨u - v, by rw [hu, hv]; ring⟩
  refine ⟨m, B, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  simp only [map_add, map_mul, map_intCast]
  change (y : K) = (m : K) + (B : K) * ((1 + x) / 2)
  rw [hab]
  have ha2 : (2 : K) * a = A := by exact_mod_cast hA.symm
  have hb2 : (2 : K) * b = B := by exact_mod_cast hB.symm
  have hm2 : (A : K) - B = 2 * m := by exact_mod_cast hm
  linear_combination (1 / 2 : K) * ha2 + (x / 2) * hb2 + (1 / 2 : K) * hm2

theorem discr_K (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) :
    NumberField.discr K = -(d : ℤ) := covA_discr K d hd4 x hx hK

theorem latI_top_basis (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ ⊤ 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = Real.sqrt d / 2 := by
  obtain ⟨ω, hω, hspan⟩ := covA_span K d hd4 x hx hK
  have hd0 : 0 < d := (Fact.out : d.Prime).pos
  have hφx : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx]; simp
  have ht := covA_sq_im (φ x) d hd0 hφx
  have key : ∀ ω' : 𝓞 K, (∀ y : 𝓞 K, ∃ m n : ℤ, y = (m : 𝓞 K) + (n : 𝓞 K) * ω') →
      latI φ ⊤ 1 = AddSubgroup.closure {1, φ (ω' : K)} := by
    intro ω' hsp
    apply le_antisymm
    · rw [latI, AddSubgroup.closure_le]
      rintro w ⟨c, -, rfl⟩
      obtain ⟨m, n, rfl⟩ := hsp c
      have e : (1 : ℂ) * φ (((m : 𝓞 K) + (n : 𝓞 K) * ω' : 𝓞 K) : K) =
          m • (1 : ℂ) + n • φ (ω' : K) := by
        push_cast
        simp [zsmul_eq_mul]
      rw [e]
      exact add_mem (zsmul_mem (AddSubgroup.subset_closure (Set.mem_insert _ _)) m)
        (zsmul_mem (AddSubgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) n)
    · rw [AddSubgroup.closure_le]
      rintro w (rfl | rfl)
      · exact AddSubgroup.subset_closure ⟨1, Submodule.mem_top, by simp⟩
      · exact AddSubgroup.subset_closure ⟨ω', Submodule.mem_top, by simp⟩
  have hωc : φ (ω : K) = (1 + φ x) / 2 := by rw [hω, map_div₀, map_add, map_one, map_ofNat]
  rcases lt_or_ge 0 (φ x).im with hpos | hneg
  · refine ⟨1, φ (ω : K), ?_, key ω hspan, ?_⟩
    · simp [hωc]
      linarith
    · have hs : Real.sqrt d = (φ x).im := by
        rw [← ht, Real.sqrt_sq hpos.le]
      simp [hωc, hs]
  · have hneg' : (φ x).im < 0 := by
      rcases hneg.lt_or_eq with h | h
      · exact h
      · rw [h] at ht
        have : (0 : ℝ) < d := by exact_mod_cast hd0
        nlinarith
    refine ⟨1, φ ((1 - ω : 𝓞 K) : K), ?_, key (1 - ω) ?_, ?_⟩
    · simp [hωc]
      linarith
    · intro y
      obtain ⟨m, n, rfl⟩ := hspan y
      exact ⟨m + n, -n, by push_cast; ring⟩
    · have hs : Real.sqrt d = -(φ x).im := by
        rw [← ht, ← neg_sq, Real.sqrt_sq (by linarith)]
      have h1ω : φ ((1 - ω : 𝓞 K) : K) = (1 - φ x) / 2 := by
        push_cast
        rw [map_sub, map_one, hωc]
        ring
      rw [h1ω, hs]
      simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem ib_im_conj_mul (u v : ℂ) : ((starRingEnd ℂ) u * v).im = u.re * v.im - u.im * v.re := by
  simp [Complex.mul_im]; ring

theorem ib_mem_range {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (w : ℂ)
    (hw : w ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)) :
    ∃ c : 𝓞 K, (φ.comp (algebraMap (𝓞 K) K)) c = w := by
  rw [← h₀] at hw
  have hle : latI φ ⊤ 1 ≤ (φ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom.range := by
    unfold latI
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, by simp⟩
  obtain ⟨c, hc⟩ := hle hw
  exact ⟨c, hc⟩

theorem ib_exists_basis {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) :
    ∃ B : Module.Basis (Fin 2) ℤ (𝓞 K), (φ.comp (algebraMap (𝓞 K) K)) (B 0) = a₀ ∧
      (φ.comp (algebraMap (𝓞 K) K)) (B 1) = b₀ := by
  obtain ⟨e, he⟩ := ib_mem_range φ a₀ b₀ h₀ a₀ (AddSubgroup.subset_closure (by simp))
  obtain ⟨f, hf⟩ := ib_mem_range φ a₀ b₀ h₀ b₀ (AddSubgroup.subset_closure (by simp))
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  have hinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hli : LinearIndependent ℤ ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : ℂ) * a₀ + (t : ℂ) * b₀ = 0 := by
      have := congrArg ψ hst
      simpa [map_add, map_zsmul, he, hf, zsmul_eq_mul] using this
    rw [ib_im_conj_mul] at hab₀
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    constructor
    · have : (s : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination b₀.im * hre - b₀.re * him
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
    · have : (t : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination a₀.re * him - a₀.im * hre
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![e, f]) := by
    intro c _
    have hc : ψ c ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ) := by
      rw [← h₀]
      exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, by simp [hψ]⟩
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hc
    have : c = m • e + n • f := hinj (by rw [← hmn]; simp [map_add, he, hf, zsmul_eq_mul])
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩ <;> simp [he, hf]

theorem ib_im_det {K : Type} [Field K] [NumberField K] (ψ : 𝓞 K →+* ℂ) (a₀ b₀ : ℂ)
    (B : Module.Basis (Fin 2) ℤ (𝓞 K)) (hB0 : ψ (B 0) = a₀) (hB1 : ψ (B 1) = b₀)
    (v : Fin 2 → 𝓞 K) :
    ((starRingEnd ℂ) (ψ (v 0)) * ψ (v 1)).im = (B.det v : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  have hv : ∀ j, ψ (v j) = (B.repr (v j) 0 : ℂ) * a₀ + (B.repr (v j) 1 : ℂ) * b₀ := by
    intro j
    conv_lhs => rw [← B.sum_repr (v j)]
    simp [Fin.sum_univ_two, map_add, hB0, hB1, zsmul_eq_mul]
  rw [Module.Basis.det_apply, Matrix.det_fin_two, hv 0, hv 1]
  simp only [Module.Basis.toMatrix_apply, ib_im_conj_mul]
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im]
  ring

theorem latI_basis (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (a₀ b₀ : ℂ) (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  obtain ⟨B, hB0, hB1⟩ := ib_exists_basis φ a₀ b₀ hab₀ h₀
  set bI := Ideal.selfBasis B 𝔞 h𝔞
  have hdet := Ideal.natAbs_det_basis_change B 𝔞 bI
  set D := B.det ((↑) ∘ bI) with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hdet
    exact h𝔞 (Ideal.absNorm_eq_zero_iff.mp hdet.symm)
  have hcross := ib_im_det ψ a₀ b₀ B hB0 hB1 ((↑) ∘ bI)
  rw [← hD] at hcross
  simp only [Function.comp_apply] at hcross
  have hN : (Ideal.absNorm 𝔞 : ℝ) = |(D : ℝ)| := by
    rw [← hdet, Nat.cast_natAbs, Int.cast_abs]
  have hlat : latI φ 𝔞 1 = AddSubgroup.closure {ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K)} := by
    apply le_antisymm
    · unfold latI
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [one_mul, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
      have hs := bI.sum_repr ⟨c, hc⟩
      have hc' : c = (bI.repr ⟨c, hc⟩ 0) • (bI 0 : 𝓞 K) + (bI.repr ⟨c, hc⟩ 1) • (bI 1 : 𝓞 K) := by
        have h2 : ((∑ i, bI.repr ⟨c, hc⟩ i • bI i : 𝔞) : 𝓞 K) = c := by rw [hs]
        rw [Fin.sum_univ_two] at h2
        exact h2.symm
      refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
      show _ = ψ c
      conv_rhs => rw [hc']
      simp [map_add]
    · rw [AddSubgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨AddSubgroup.subset_closure ⟨_, (bI 0).2, by simp [hψ]⟩,
        AddSubgroup.subset_closure ⟨_, (bI 1).2, by simp [hψ]⟩⟩
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · have hneg' : (D : ℝ) < 0 := by exact_mod_cast hneg
    have hsw : ((starRingEnd ℂ) (ψ (bI 1 : 𝓞 K)) * ψ (bI 0 : 𝓞 K)).im =
        -((starRingEnd ℂ) (ψ (bI 0 : 𝓞 K)) * ψ (bI 1 : 𝓞 K)).im := by
      rw [ib_im_conj_mul, ib_im_conj_mul]; ring
    refine ⟨ψ (bI 1 : 𝓞 K), ψ (bI 0 : 𝓞 K), ?_, by rw [hlat, Set.pair_comm], ?_⟩
    · rw [hsw, hcross]; nlinarith
    · rw [hsw, hcross, hN, abs_of_neg hneg']; ring
  · have hpos' : (0 : ℝ) < D := by exact_mod_cast hpos
    refine ⟨ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K), ?_, hlat, ?_⟩
    · rw [hcross]; positivity
    · rw [hcross, hN, abs_of_pos hpos']

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

lemma conj_mul_im_eq_normSq_mul_div_im (a b : ℂ) (ha : a ≠ 0) :
    ((starRingEnd ℂ) a * b).im = Complex.normSq a * (b / a).im := by
  have hn : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

lemma ne_zero_and_div_im_pos (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    a ≠ 0 ∧ 0 < (b / a).im := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  refine ⟨ha, ?_⟩
  rw [conj_mul_im_eq_normSq_mul_div_im a b ha] at hab
  exact pos_of_mul_pos_right hab (Complex.normSq_nonneg a)

theorem discr_closure_pair_ne_zero (a b : ℂ) (hab : 0 < ((starRingEnd ℂ) a * b).im) :
    discr (AddSubgroup.closure {a, b}) ≠ 0 := by
  obtain ⟨ha, hpos⟩ := ne_zero_and_div_im_pos a b hab
  rw [discr_closure_pair a b hpos]
  have hpi : (2 * Real.pi / a : ℂ) ≠ 0 := by
    refine div_ne_zero ?_ ha
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_ne_zero (pow_ne_zero _ hpi) (pow_ne_zero _ (ModularForm.eta_ne_zero hpos))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem exists_latI_basis (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt d / 2 := by
  obtain ⟨a₀, b₀, h₀, hl₀, hc₀⟩ := latI_top_basis K d hd4 x hx hK φ
  obtain ⟨a, b, h, hl, hc⟩ := latI_basis K hK φ a₀ b₀ h₀ hl₀ 𝔞 h𝔞
  exact ⟨a, b, h, hl, by rw [hc, hc₀]; ring⟩

theorem discr_latI_ne_zero (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    discr (latI φ 𝔞 1) ≠ 0 := by
  obtain ⟨a, b, h, hl, -⟩ := exists_latI_basis K d hd4 x hx hK φ 𝔞 h𝔞
  rw [hl]; exact discr_closure_pair_ne_zero a b h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end
