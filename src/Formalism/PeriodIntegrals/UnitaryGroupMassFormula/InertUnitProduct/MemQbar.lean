import Mathlib
import Formalism.PeriodIntegrals.ProdUnitInert

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ProdUnitInert

variable {p : ℕ} [Fact p.Prime]

lemma not_small_sq_add (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (t : ℤ_[p]) :
    ¬ ‖t ^ 2 + (d : ℤ_[p])‖ < 1 := by
  intro h
  have hmem : t ^ 2 + (d : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]; exact h
  rw [RingHom.mem_ker, map_add, map_pow, map_natCast] at hmem
  apply hd
  refine ⟨PadicInt.toZMod t, ?_⟩
  push_cast
  linear_combination (-1 : ZMod p) * hmem

lemma natCast_norm_le_one (d : ℕ) : ‖(d : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (d : ℤ)

lemma y_norm_le_one (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (X Y : ℚ_[p])
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖Y‖ ≤ 1 := by
  by_contra hY
  push Not at hY
  have hY0 : Y ≠ 0 := by
    rintro rfl
    simp at hY
    linarith
  have key : (X / Y) ^ 2 + d = 1 / Y ^ 2 := by
    rw [div_pow]
    field_simp
    linear_combination h
  have hsmall : ‖(X / Y) ^ 2 + (d : ℚ_[p])‖ < 1 := by
    rw [key, norm_div, norm_one, norm_pow]
    have : 1 < ‖Y‖ ^ 2 := by nlinarith
    rw [div_lt_one (by linarith)]
    exact this
  have ht1 : ‖X / Y‖ ≤ 1 := by
    by_contra ht1
    push Not at ht1
    have h2 : 1 < ‖(X / Y) ^ 2‖ := by rw [norm_pow]; nlinarith
    have hd1 := natCast_norm_le_one (p := p) d
    have hne : ‖(X / Y) ^ 2‖ ≠ ‖(d : ℚ_[p])‖ := by intro h'; linarith
    rw [Padic.add_eq_max_of_ne hne] at hsmall
    have := le_max_left ‖(X / Y) ^ 2‖ ‖(d : ℚ_[p])‖
    linarith
  let T : ℤ_[p] := ⟨X / Y, ht1⟩
  apply not_small_sq_add d hd T
  have hc : (((T ^ 2 + (d : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) = (X / Y) ^ 2 + d := by
    have hT : (T : ℚ_[p]) = X / Y := rfl
    rw [PadicInt.coe_add, PadicInt.coe_pow, hT, PadicInt.coe_natCast]
  rw [PadicInt.norm_def, hc]
  exact hsmall

lemma x_norm_le_one (d : ℕ) (X Y : ℚ_[p]) (hY : ‖Y‖ ≤ 1)
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖X‖ ≤ 1 := by
  have hX2 : X ^ 2 = 1 + (-(d * Y ^ 2)) := by linear_combination h
  have hd1 := natCast_norm_le_one (p := p) d
  have hle : ‖X‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hX2]
    refine (Padic.nonarchimedean _ _).trans (max_le (le_of_eq norm_one) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h0 : ‖Y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Y]
    nlinarith [norm_nonneg (d : ℚ_[p]), norm_nonneg Y, sq_nonneg ‖Y‖]
  nlinarith [norm_nonneg X]

lemma normC_ratCast (q : ℚ) : ‖(q : ℂ_[p])‖ = ‖(q : ℚ_[p])‖ := by
  have hc : (((q : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (q : ℂ_[p]) := by
    simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← hc, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem norm_conic_eq_one (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (x y : ℚ)
    (hxy : x ^ 2 + d * y ^ 2 = 1) (γ : ℂ_[p]) (hγ : γ ^ 2 = -(d : ℂ_[p])) :
    ‖(x : ℂ_[p]) + y * γ‖ = 1 := by
  have hQ : (x : ℚ_[p]) ^ 2 + d * (y : ℚ_[p]) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℚ_[p])) hxy
  have hy := y_norm_le_one d hd _ _ hQ
  have hx := x_norm_le_one d _ _ hy hQ
  have hy' : ‖(y : ℂ_[p])‖ ≤ 1 := by rw [normC_ratCast]; exact hy
  have hx' : ‖(x : ℂ_[p])‖ ≤ 1 := by rw [normC_ratCast]; exact hx
  have hdC : ‖(d : ℂ_[p])‖ ≤ 1 := by
    have h1 := normC_ratCast (p := p) (d : ℚ)
    push_cast at h1
    rw [h1]
    exact natCast_norm_le_one d
  have hγ1 : ‖γ‖ ≤ 1 := by
    have h2 : ‖γ‖ ^ 2 ≤ 1 := by rw [← norm_pow, hγ, norm_neg]; exact hdC
    nlinarith [norm_nonneg γ]
  have hC : (x : ℂ_[p]) ^ 2 + d * (y : ℂ_[p]) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ_[p])) hxy
  have hprod : ((x : ℂ_[p]) + y * γ) * ((x : ℂ_[p]) - y * γ) = 1 := by
    linear_combination hC - (y : ℂ_[p]) ^ 2 * hγ
  have hyγ : ‖(y : ℂ_[p]) * γ‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (y : ℂ_[p]), norm_nonneg γ]
  have hA : ‖(x : ℂ_[p]) + y * γ‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hyγ)
  have hB : ‖(x : ℂ_[p]) - y * γ‖ ≤ 1 :=
    sub_eq_add_neg (x : ℂ_[p]) (y * γ) ▸
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' (by rwa [norm_neg]))
  have hAB : ‖(x : ℂ_[p]) + y * γ‖ * ‖(x : ℂ_[p]) - y * γ‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  refine le_antisymm hA ?_
  nlinarith [norm_nonneg ((x : ℂ_[p]) + y * γ), norm_nonneg ((x : ℂ_[p]) - y * γ)]

end PI.UnitaryGroupMassFormula.ProdUnitInert
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ProdUnitInert

lemma conj_eq_neg_of_sq (d : ℕ) (β : ℂ) (hβ : β ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) β = -β := by
  have h1 := congrArg Complex.re hβ
  have h2 := congrArg Complex.im hβ
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hre : β.re = 0 := by
    have hri : β.re * β.im = 0 := by linarith
    rcases mul_eq_zero.mp hri with h | h
    · exact h
    · rw [h] at h1
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [sq_nonneg β.re]
  apply Complex.ext <;> simp [hre]

lemma conic_of_norm_one (d : ℕ) (β : ℂ) (hβ : β ^ 2 = -(d : ℂ)) (x y : ℚ)
    (h : ((x : ℂ) + y * β) * (starRingEnd ℂ) ((x : ℂ) + y * β) = 1) :
    x ^ 2 + d * y ^ 2 = 1 := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, conj_eq_neg_of_sq d β hβ] at h
  have hC : ((x ^ 2 + d * y ^ 2 : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by
    push_cast
    linear_combination h + (y : ℂ) ^ 2 * hβ
  exact_mod_cast hC

lemma exists_rat_coords {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E)
    (hK : Module.finrank ℚ K = 2) (d : ℕ) (hd : d ≠ 0) (b : K)
    (hb : b ^ 2 = ((-(d : ℤ) : ℤ) : K)) (w : K) :
    ∃ x y : ℚ, w = (x : K) + (y : K) * b := by
  let v : Fin 2 → K := ![1, b]
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Rat.smul_def, mul_one] at hg
    have h1 : g 1 = 0 := by
      by_contra h1
      have hg1 : ((g 1 : ℚ) : K) ≠ 0 := by exact_mod_cast h1
      have hmul : ((g 1 : ℚ) : K) * b = -((g 0 : ℚ) : K) := by linear_combination hg
      have hbq : b = ((-(g 0 / g 1) : ℚ) : K) := by
        rw [(eq_inv_mul_iff_mul_eq₀ hg1).mpr hmul]
        push_cast
        ring
      have hsq : (((-(g 0 / g 1)) ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K) := by
        rw [Rat.cast_pow, ← hbq, hb]
        push_cast
        ring
      have hq := Rat.cast_injective hsq
      have hd' : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
      nlinarith [sq_nonneg (-(g 0 / g 1))]
    have h0 : g 0 = 0 := by
      rw [h1] at hg
      have : ((g 0 : ℚ) : K) = 0 := by simpa using hg
      exact_mod_cast this
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ K := by simp [hK]
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum := B.sum_repr w
  rw [hB, Fin.sum_univ_two] at hsum
  refine ⟨B.repr w 0, B.repr w 1, hsum.symm.trans ?_⟩
  simp [v, Rat.smul_def]

theorem prod_emb_eq_norm {E : Type} [Field E] [NumberField E] (K : IntermediateField ℚ E)
    (φ₀ : E →+* ℂ) (S : Type) [Fintype S] (emb : S → E →+* ℂ) (hinj : Function.Injective emb)
    (hagree : ∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E))
    (hcard : Fintype.card S = Module.finrank K E) (z : E) :
    ∏ s, emb s z = φ₀ ((Algebra.norm K z : K) : E) := by
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  let f : S → (E →ₐ[K] ℂ) := fun s =>
    { toRingHom := emb s
      commutes' := fun a => by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
        exact hagree s a }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext e
    exact DFunLike.congr_fun hst e
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf, by rw [AlgHom.card, hcard]⟩
  have h1 := Algebra.norm_eq_prod_embeddings (K := K) (E := ℂ) z
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at h1
  calc ∏ s, emb s z = ∏ s, f s z := rfl
    _ = ∏ σ : E →ₐ[K] ℂ, σ z := Fintype.prod_bijective f hbij _ _ (fun _ => rfl)
    _ = _ := h1.symm

end PI.UnitaryGroupMassFormula.ProdUnitInert
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.ProdUnitInert

open PI.ProdUnitInert

lemma mem_Qbar {E : Type} [Field E] [NumberField E] (φ₀ : E →+* ℂ) (e : E) :
    φ₀ e ∈ Qbar := by
  rw [Qbar, mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) e).map φ₀.toRatAlgHom

theorem main : PI.ProdUnitInert := by
  intro E _ _ K c φ₀ S _ emb hinj hagree hcard hc hK d p _ b hb hjac lam z hz
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : jacobiSym 0 p = 0 := jacobiSym.zero_left (Fact.out : p.Prime).one_lt
    simp [h0] at hjac
  have hns : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p)) :=
    (legendreSym.eq_neg_one_iff (p := p)).mp (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hjac)
  have hP := prod_emb_eq_norm K φ₀ S emb hinj hagree hcard z
  obtain ⟨x, y, hw⟩ := exists_rat_coords K hK d hd0 b hb (Algebra.norm K z)
  have hβ : (φ₀ (b : E)) ^ 2 = -(d : ℂ) := by
    have h := congrArg (fun t : K => φ₀ (t : E)) hb
    simpa using h
  have hPxy : ∏ s, emb s z = (x : ℂ) + y * φ₀ (b : E) := by
    rw [hP, hw]
    simp
  have hPP : (∏ s, emb s z) * (starRingEnd ℂ) (∏ s, emb s z) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun s _ => by rw [← hc, ← map_mul, hz, map_one])
  rw [hPxy] at hPP
  have hconic := conic_of_norm_one d _ hβ x y hPP
  have hβmem : φ₀ (b : E) ∈ Qbar := mem_Qbar φ₀ _
  have hPmem : (∏ s, emb s z) ∈ Qbar := by rw [hP]; exact mem_Qbar φ₀ _
  unfold PI.ProdUnitInert.lamC
  rw [dif_pos hPmem]
  have hsub : (⟨∏ s, emb s z, hPmem⟩ : Qbar) = (x : Qbar) + (y : Qbar) * ⟨φ₀ (b : E), hβmem⟩ := by
    apply Subtype.ext
    simp [hPxy]
  rw [hsub, map_add, map_mul, map_ratCast, map_ratCast]
  apply norm_conic_eq_one d hns x y hconic
  have hsq : (⟨φ₀ (b : E), hβmem⟩ : Qbar) ^ 2 = -(d : Qbar) := by
    apply Subtype.ext
    simp [hβ]
  rw [← map_pow, hsq, map_neg, map_natCast]

end PI.UnitaryGroupMassFormula.ProdUnitInert
end
end
