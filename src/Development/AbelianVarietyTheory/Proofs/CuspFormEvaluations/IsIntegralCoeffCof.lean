import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameLetterGLActionRepresentationKeepsHarmonic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemOfForallLocP
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightVariableFormula
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemNabStdOfDetMulIntegral

section
set_option autoImplicit false

namespace GlobalTheory.CMTypeOrConjugate

open NumberField

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exfalso
    obtain ⟨x, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h2 : x ^ 2 = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg x]
  · exact h

theorem inPsi_or_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    Formalism.L2.Pj.InPsi H τ ∨ Formalism.L2.Pj.InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hz : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hE, map_neg, map_natCast]
  unfold Formalism.L2.Pj.InPsi
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, conj_eq_neg_of_sq H.d_prime.pos hz, h, neg_neg]

end GlobalTheory.CMTypeOrConjugate
end

section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FrameRead

theorem inPsi_or_conjugate_unit {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  first
  | exact @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate
  | (apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMTypeOrConjugate.inPsi_or_inPsi_conjugate ..)

theorem gaStar_conj_eq_letAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (ga : Matrix (Fin n) (Fin n) E) (h : IsUnit ga.det), ga.conjTranspose * ga = 1 → gaStar (Dw := Dw) c (ga.map (IsCMField.complexConj E)) = letAct Dw pl c.F (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) := by
  intro E _ _ _ H Dw n Ix _ pl hpl _ l c ga h hU
  have hval : ((Matrix.nonsingInvUnit ga h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = ga := rfl
  have hinv : (((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
      = ga.conjTranspose := by
    rw [Matrix.coe_units_inv, hval]
    exact Matrix.inv_eq_left_inv hU
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, i, b⟩
  simp only [Formalism.L2.Pj.gaStar, letAct, aeval_X, letB]
  split_ifs with h1 h2
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h1.choose :
        Matrix (Fin n) (Fin n) c.F) j b = embF c (pl h1.choose)
          ((((Matrix.nonsingInvUnit ga h : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b j) := rfl
    rw [e, hinv, h1.choose_spec]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    have e : (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) h2.choose)⁻¹ : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F) b j = embF c (pl h2.choose) (ga j b) := rfl
    rw [e]
    apply Subtype.ext
    change τ (IsCMField.complexConj E (ga j b)) = pl h2.choose (ga j b)
    have hs := h2.choose_spec
    generalize h2.choose = t at hs ⊢
    subst hs
    rw [IsCMField.complexEmbedding_complexConj]
    simp
  · exfalso
    rcases inPsi_or_conjugate_unit H τ with h3 | h3
    · exact h1 ((hpl.2 τ).1 h3)
    · obtain ⟨t, ht⟩ := (hpl.2 _).1 h3
      exact h2 ⟨t, by rw [ht]; ext x; simp⟩

end GlobalTheory.FrameRead
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Harm
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ}

def invTranspose {K : Type} [Field K] (g : GL (Fin n) K) : GL (Fin n) K :=
  ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose, (g : Matrix (Fin n) (Fin n) K).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem rename_letAct_invTranspose_eq_colAct {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)} (hpl : IsEnum H pl) (K : Type) [Field K]
    (g : {τ : E →+* ℂ // InPsi H τ} → GL (Fin n) K) (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩)) P) =
      colAct K _ Dw.p Dw.q (Fin n) g (rename (thetaLetterEquiv Dw n) P) := by
  rw [colAct_apply]
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp
    (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩))) =
    (colSubst (fun t => (((g t)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (fun t => g t)).comp
      (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with h | ⟨τ, h, rfl⟩
  · have h₁ : ∃ t, pl t = τ := (hpl.2 τ).1 h
    rw [dif_pos h₁, thetaLetterEquiv_of_mem Dw h, colSubst_X_xVar, xForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext h₁.choose_spec
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw h]
    simp only [e]
    rfl
  · have h₀ : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun hh => by
      have h₂ : InPsi H (ComplexEmbedding.conjugate τ) := (hpl.2 _).2 hh
      exact (not_mem_hostType_iff H τ).2 h₂ h
    have h₁ : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ := by
      obtain ⟨t, ht⟩ := (hpl.2 τ).1 h
      exact ⟨t, by rw [ht]⟩
    rw [dif_neg h₀, dif_pos h₁, thetaLetterEquiv_conjugate Dw h, colSubst_X_yVar, yForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext ((ComplexEmbedding.involutive_conjugate E).injective h₁.choose_spec)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw h]
    simp only [e]
    rfl

variable {l : Level H} (c : Coeff l)

theorem rename_minorP_of_mem (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.p)
    (hi : i.val < Dw.mult τ) (hi' : i.val + 1 ≤ n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c τ i.val hi (Fin.castLE hi')) =
      xMinor ⟨τ, h⟩ i (baseCovec c.F hn) := by
  rw [minorPolynomial, xMinor, AlgHom.map_det]
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseCovec, xForm_single]
  rw [thetaLetterEquiv_of_mem Dw h]
  rfl

theorem rename_minorP_conjugate (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.q)
    (hi : i.val < Dw.mult (ComplexEmbedding.conjugate τ)) (hi' : n - (i.val + 1) + (i.val + 1) = n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c (ComplexEmbedding.conjugate τ) i.val hi
      (fun b => Fin.cast hi' (Fin.natAdd (n - (i.val + 1)) b))) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        yMinor ⟨τ, h⟩ i (baseVec c.F hn) := by
  rw [minorPolynomial, yMinor, AlgHom.map_det, ← Matrix.det_permute']
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseVec, yForm_single,
    Matrix.submatrix_apply, id]
  rw [thetaLetterEquiv_conjugate Dw h]
  refine congrArg X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

theorem rename_pG [Fintype {τ : E →+* ℂ // InPsi H τ}] (hn : Dw.p + Dw.q ≤ n) (a : (E →+* ℂ) × ℕ → ℕ) :
    ∃ u : ℤˣ, rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) =
      ((u : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        basePoly c.F hn (fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i))
          (fun t => diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) := by
  refine ⟨∏ t : {τ : E →+* ℂ // InPsi H τ}, ∏ i : Fin Dw.q, Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) ^
    diffOf (fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) i, ?_⟩
  rw [pG, ← Fintype.prod_sigma', ← (halfRowEquiv (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw)).symm.prod_comp,
    Fintype.prod_prod_type, basePoly, minorProd, map_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Fintype.prod_sum_type, map_mul, mul_left_comm, ← Finset.prod_mul_distrib, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult t.1 := by rw [mult_of_mem Dw t.2]; exact i.isLt
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H t.1 then minorPolynomial c t.1 i.val hi (Fin.castLE h)
        else minorPolynomial c t.1 i.val hi (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a t.1 i.val) = _
    rw [dif_pos hi', if_pos t.2, map_pow, rename_minorP_of_mem Dw c hn t.2]
    congr 1
    rw [aStep, diffOf, mult_of_mem Dw t.2]
    split_ifs <;> rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult (ComplexEmbedding.conjugate t.1) :=
      i.isLt.trans_eq (mult_conjEmb_of_mem Dw t.2).symm
    have h₀ : ¬ InPsi H (ComplexEmbedding.conjugate t.1) := fun h₂ => (not_mem_hostType_iff H t.1).2 h₂ t.2
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H (ComplexEmbedding.conjugate t.1) then
        minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi (Fin.castLE h)
        else minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi
          (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a (ComplexEmbedding.conjugate t.1) i.val) = _
    rw [dif_pos hi', if_neg h₀, map_pow, rename_minorP_conjugate Dw c hn t.2, ← mul_pow]
    congr 1
    have hq : Dw.mult (ComplexEmbedding.conjugate t.1) = Dw.q := mult_conjEmb_of_mem Dw t.2
    rw [aStep, diffOf, hq]
    split_ifs <;> rfl

theorem pG_mem_ne_zero_generates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → pG (Dw := Dw) c a n ∈ harmA (Dw := Dw) c a n ∧ pG (Dw := Dw) c a n ≠ 0 ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F => letAct Dw pl c.F g (pG (Dw := Dw) c a n)) := by
  intro E _ _ _ H Dw n Ix _ pl hpl hn l c a ha
  obtain ⟨u, hu⟩ := rename_pG Dw c hn a
  set k := fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i) with hk
  set k' := fun t : {τ : E →+* ℂ // InPsi H τ} =>
    diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) with hk'
  have hx (t : {τ : E →+* ℂ // InPsi H τ}) : partOf (k t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j hij => ha t.1 hij
  have hy (t : {τ : E →+* ℂ // InPsi H τ}) :
      partOf (k' t) = fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j hij => ha _ hij
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        rename (thetaLetterEquiv Dw n) P ∈ orbitSpan c.F hn k k' := by
    rw [← (rowHighest_orbitSpan_main hn k k' c.F).2.1, mem_rowHighest_iff_rowAdd]
    simp only [hx, hy]
    exact mem_HHa_iff_rename (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) _ P
  rw [← zsmul_eq_mul] at hu
  have hu' : basePoly c.F hn k k' = (u : ℤ) • rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) := by
    rw [hu, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  have hinj := (thetaLetterEquiv Dw n).injective
  refine ⟨⟨(hmem _).2 ?_, fun m => ?_⟩, fun h0 => ?_, fun P hP => ?_⟩
  · rw [hu]
    exact zsmul_mem (basePoly_mem hn k k') _
  · rw [← coeff_rename_mapDomain _ hinj, hu, ← map_basePoly hn k k' (Int.castRingHom c.F), ← map_zsmul, coeff_map]
    exact intCast_mem _ _
  · rw [h0, map_zero, smul_zero] at hu'
    exact basePoly_ne_zero hn k k' hu'
  · have key : orbitSpan c.F hn k k' ≤ (Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F =>
        letAct Dw pl c.F g (pG (Dw := Dw) c a n))).map (rename (thetaLetterEquiv Dw n)).toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      simp only [hu', map_zsmul, ← rename_letAct_invTranspose_eq_colAct Dw hpl]
      exact zsmul_mem (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self _))) _
    obtain ⟨Q, hQ, e⟩ := key ((hmem P).1 hP)
    rwa [← rename_injective _ hinj e]

end GlobalTheory.FrameRead
end
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Classical Matrix

def hhaSub {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Submodule k (MvPolynomial (Letter T r n) k) where
  carrier := HHa r n k cc isX a
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ _ => map_zero _, fun m hm => by simp at hm⟩
  add_mem' := by
    intro P Q hP hQ
    refine ⟨add_mem hP.1 hQ.1, fun σ i i' h t => ?_, fun m hm => ?_⟩
    · rw [map_add, hP.2.1 σ i i' h t, hQ.2.1 σ i i' h t]
    · rcases Finset.mem_union.1 (support_add hm) with h | h
      · exact hP.2.2 m h
      · exact hQ.2.2 m h
  smul_mem' := by
    intro c P hP
    refine ⟨Submodule.smul_mem _ c hP.1, fun σ i i' h t => ?_, fun m hm => hP.2.2 m (support_smul hm)⟩
    rw [map_smul, hP.2.1 σ i i' h t]

theorem det_gen_ne_zero {K : Type} [Field K] {Ix : Type} {n : ℕ} (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)) h
  rw [RingHom.map_det] at h2
  have : (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)).mapMatrix
      (gen K n t) = 1 := by
    ext1 i j
    simp [gen]
  rw [this] at h2
  simp at h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero t)

theorem cof_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first
  | exact @_root_.GlobalTheory.WeightOrderLemmas.main
  | exact _root_.GlobalTheory.WeightOrderLemmas.main
  | (apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightOrderLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightOrderLemmas.main ..)

end GlobalTheory.FrameRead
end
end

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_weight_dominance_condition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  atlas_forward_decl GlobalTheory.FrameRead.cof_image
end

section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.FrameRead.CoefMap

def harmSub {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Submodule k (MvPolynomial (Letter T r n) k) where
  carrier := HHa r n k cc isX a
  add_mem' := by
    rintro P Q ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨add_mem h1 h1', fun σ i i' h t => by rw [map_add, h2 σ i i' h t, h2' σ i i' h t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact h3 m h
    · exact h3' m h
  zero_mem' := ⟨zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩
  smul_mem' := by
    rintro x P ⟨h1, h2, h3⟩
    exact ⟨Submodule.smul_mem _ x h1, fun σ i i' h t => by rw [map_smul, h2 σ i i' h t],
      fun m hm => h3 m (support_smul hm)⟩

theorem det_gen_ne_zero (K : Type) [Field K] {Ix : Type} (n : ℕ) (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)).mapMatrix (gen K n t) = 1 := by
    ext p q
    simp [gen, Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem map_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {Ix : Type} (n : ℕ) (t : Ix) :
    (MvPolynomial.map f).mapMatrix (gen R n t) = gen S n t := by
  ext p q : 2
  simp [gen]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {n : ℕ}
  {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero K n t)

theorem map_cof {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Q : MvPolynomial (LtN Dw n) R) :
    MvPolynomial.map f (cof Dw pl R n Q) = cof Dw pl S n (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [algHom_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ℓ hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cof, aeval_X]
    split_ifs with h1 h2 h3
    · simp [gen]
    · rw [← map_gen f, ← RingHom.map_adjugate]
      rfl
    · simp
    · simp

theorem isIntegral_coeff_cof {K : Type} [Field K] (P : MvPolynomial (LtN Dw n) K)
    (hP : ∀ m, P.coeff m ∈ (integralClosure ℤ K).toSubring) (m) : IsIntegral ℤ ((cof Dw pl K n P).coeff m) := by
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.map (integralClosure ℤ K).toSubring.subtype Q = P := by
    refine ⟨∑ m ∈ P.support, monomial m ⟨P.coeff m, hP m⟩, ?_⟩
    simp only [map_sum, map_monomial, Subring.subtype_apply]
    exact P.as_sum.symm
  rw [← map_cof, coeff_map]
  exact ((cof Dw pl _ n Q).coeff m).2

set_option maxHeartbeats 1000000 in

theorem exists_ioLFRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw := by
  intro E _ _ _ H Dw n Ix _ pl he hn l c a s lam ha hwt
  obtain ⟨ε, hε⟩ := GlobalTheory.T.frameReading_leadingMinorProduct_extremal E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨him, hex, heq⟩ := GlobalTheory.T.hodge_weight_dominance_condition E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨hpG, -, -⟩ := pG_mem_ne_zero_generates E H Dw n Ix pl he hn l c a ha
  obtain ⟨-, -, hstab⟩ := letAct_mul_one_mem_HHa E H Dw n Ix pl he hn c.F a
  obtain ⟨hs1, hs2, hs3⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c.F Ix n (fun t => embF c (pl t)) lam
  have hD := detFac_ne_zero Dw pl c.F a s lam
  let S := harmSub Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
  have hS : ∀ P, P ∈ S ↔ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) :=
    fun _ => Iff.rfl
  set e : c.F := ((ε : ℤ) : c.F) with he'
  have hee : e * e = 1 := by
    rw [he', ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have heI : IsIntegral ℤ e := isIntegral_intCast _
  set D := detFac Dw pl c.F a s lam with hDdef
  have hex' : ∀ F : VVc c lam, ∃! P, P ∈ S ∧ cof Dw pl c.F n P = e • (D * F.1) := fun F => by
    have := hex (e • F.1) (Submodule.smul_mem _ _ F.2)
    rwa [mul_smul_comm] at this
  choose φ hφ huniq using hex'
  have hu : ∀ (F : VVc c lam) P, P ∈ S → cof Dw pl c.F n P = e • (D * F.1) → φ F = P :=
    fun F P h1 h2 => (huniq F P ⟨h1, h2⟩).symm
  let io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F :=
    { toFun := φ
      map_add' := fun F G => hu _ _ (add_mem (hφ F).1 (hφ G).1) (by
        rw [map_add, (hφ F).2, (hφ G).2, Submodule.coe_add, mul_add, smul_add])
      map_smul' := fun x F => hu _ _ (Submodule.smul_mem _ _ (hφ F).1) (by
        rw [map_smul, (hφ F).2, Submodule.coe_smul, mul_smul_comm, smul_comm]; rfl) }
  have hio : ∀ F, io F = φ F := fun _ => rfl
  have hsurj : ∀ P ∈ S, ∃ F : VVc c lam, io F = P := fun P hP => by
    obtain ⟨F, hF, h⟩ := him P hP
    refine ⟨⟨e • F, Submodule.smul_mem _ _ hF⟩, hu _ _ hP ?_⟩
    rw [h, mul_smul_comm, smul_smul, hee, one_smul]
  have hwm : (ten fun t => extremal c.F n (lam t)) ∈ VV c.F lam := by
    obtain ⟨F, hF, h⟩ := him _ hpG.1
    rw [hε, ← mul_smul_comm] at h
    have h' := mul_left_cancel₀ hD h
    have : (ten fun t => extremal c.F n (lam t)) = e • F := by rw [← h', smul_smul, hee, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hF
  refine ⟨io, ⟨_, hwm⟩, rfl, fun ga => if h : IsUnit ga.det then
      ∏ t, (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) t : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F).det ^ (s t) else 0, hn, ?_, ?_, ?_, (hs1 _).2 hs2,
      fun x hx => hs3 x ((hs1 _).1 hx), hu _ _ hpG.1 hε, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro F hF
    have h := (hφ F).2
    rw [← hio, hF, map_zero] at h
    have h' := congrArg (fun x => e • x) h
    simp only [smul_zero, smul_smul, hee, one_smul] at h'
    exact Subtype.ext ((mul_eq_zero.1 h'.symm).resolve_left hD)
  · have : Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) = S :=
      Submodule.span_eq S
    rw [this]
    refine le_antisymm ?_ hsurj
    rintro _ ⟨F, rfl⟩
    exact (hφ F).1
  · intro ga hga F
    have h : IsUnit ga.det := by
      have := congrArg Matrix.det hga
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one_right _ this
    rw [gaStar_conj_eq_letAct E H Dw n Ix pl he hn l c ga h hga]
    simp only [dif_pos h, rhoM]
    set g := invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) with hg
    refine hu _ _ (Submodule.smul_mem _ _ (hstab g _ (hφ F).1)) ?_
    have h1 := heq g _ (hφ F).1 (e • F.1) (Submodule.smul_mem _ _ F.2) (by rw [(hφ F).2, mul_smul_comm])
    rw [map_smul, hio, h1, smul_smul, ← Finset.prod_mul_distrib, map_smul, mul_smul_comm]
    have h2 : ∏ t, (g t : Matrix (Fin n) (Fin n) c.F).det ^ (s t) * (g t : Matrix (Fin n) (Fin n) c.F).det ^ (-(s t)) = 1 :=
      Finset.prod_eq_one fun t _ => by
        rw [← zpow_add₀ (Matrix.isUnits_det_units (g t)).ne_zero, add_neg_cancel, zpow_zero]
    rw [h2, one_smul]
    rfl
  · intro P hP
    obtain ⟨F, rfl⟩ := hsurj P hP.1
    refine ⟨F, (hs1 F).2 (GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral c.F Ix n lam
      (fun t => ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat) F.1 F.2 fun m => ?_), rfl⟩
    have h : e • cof Dw pl c.F n (φ F) = D * F.1 := by rw [(hφ F).2, smul_smul, hee, one_smul]
    change IsIntegral ℤ ((D * F.1).coeff m)
    rw [← h, coeff_smul, smul_eq_mul]
    exact heI.mul (isIntegral_coeff_cof Dw pl (φ F) hP.2 m)

end GlobalTheory.FrameRead.CoefMap
end
end
