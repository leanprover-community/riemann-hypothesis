import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulOfSeparableGenerated

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E]

theorem trace_semilinear {A : Type} [CommRing A] [Algebra E A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι E A) (c : E →+* E) (hc : ∀ x, c (c x) = x) (σ : A →+* A) (hσσ : ∀ y, σ (σ y) = y)
    (hσ : ∀ e, σ (algebraMap E A e) = algebraMap E A (c e)) (a : A) :
    Algebra.trace E A (σ a) = c (Algebra.trace E A a) := by
  have hsm : ∀ (e : E) (y : A), σ (e • y) = c e • σ y := by
    intro e y; rw [Algebra.smul_def, Algebra.smul_def, map_mul, hσ]
  let e : A ≃ₗ[E] (ι → E) :=
    { toFun := fun y i => c (b.equivFun (σ y) i)
      map_add' := by intro y z; ext i; simp
      map_smul' := by intro r y; ext i; simp [hsm, hc]
      invFun := fun v => σ (b.equivFun.symm (fun i => c (v i)))
      left_inv := by
        intro y
        simp only [hc]
        show σ (b.equivFun.symm (b.equivFun (σ y))) = y
        rw [LinearEquiv.symm_apply_apply, hσσ]
      right_inv := by
        intro v
        ext i
        simp only [hσσ, LinearEquiv.apply_symm_apply, hc] }
  let b' : Module.Basis ι E A := Module.Basis.ofEquivFun e
  have hrep : ∀ y i, b'.repr y i = c (b.repr (σ y) i) := by
    intro y i
    rw [Module.Basis.ofEquivFun_repr_apply]; rfl
  have hb' : ∀ j, b' j = σ (b j) := by
    intro j
    rw [Module.Basis.coe_ofEquivFun]
    show σ (b.equivFun.symm (fun i => c ((Pi.single j (1 : E) : ι → E) i))) = σ (b j)
    congr 1
    have : (fun i => c ((Pi.single j (1 : E) : ι → E) i)) = (Pi.single j 1 : ι → E) := by
      ext i; by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [this]; simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hrep, hb', ← map_mul, hσσ]

end GlobalTheory.EllHermGlobal

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E] (c : E →+* E) (P : E[X])

def rinv : AdjoinRoot P := AdjoinRoot.mk P (C (-(P.coeff 0)⁻¹) * divX P)

theorem root_mul_rinv (h0 : P.coeff 0 ≠ 0) : AdjoinRoot.root P * rinv P = 1 := by
  have hC : C (-(P.coeff 0)⁻¹) * C (P.coeff 0) = (-1 : E[X]) := by
    rw [← C_mul, neg_mul, inv_mul_cancel₀ h0, C_neg, C_1]
  have h := divX_mul_X_add P
  have key : X * (C (-(P.coeff 0)⁻¹) * divX P) = C (-(P.coeff 0)⁻¹) * P + 1 := by
    linear_combination (C (-(P.coeff 0)⁻¹)) * h - hC
  rw [rinv, ← AdjoinRoot.mk_X, ← map_mul, key, map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one]

def sig (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) : AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap E (AdjoinRoot P)).comp c) (rinv P) (by
    letI : Invertible (rinv P) :=
      { invOf := AdjoinRoot.root P
        invOf_mul_self := root_mul_rinv P h0
        mul_invOf_self := by rw [mul_comm]; exact root_mul_rinv P h0 }
    rw [← eval₂_map, ← eval₂_reverse_eq_zero_iff, ← hr]
    have : ⅟(rinv P) = AdjoinRoot.root P := rfl
    rw [this, eval₂_mul, eval₂_C, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, mul_zero])

variable {c P}

theorem sig_root (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) :
    sig c P h0 hr (AdjoinRoot.root P) = rinv P := AdjoinRoot.lift_root _

theorem sig_alg (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) (e : E) :
    sig c P h0 hr (algebraMap E (AdjoinRoot P) e) = algebraMap E (AdjoinRoot P) (c e) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

theorem sig_sig (hc : ∀ x, c (c x) = x) (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse)
    (y : AdjoinRoot P) : sig c P h0 hr (sig c P h0 hr y) = y := by
  have hinv : sig c P h0 hr (rinv P) = AdjoinRoot.root P := by
    have h1 : sig c P h0 hr (AdjoinRoot.root P) * sig c P h0 hr (rinv P) = 1 := by
      rw [← map_mul, root_mul_rinv P h0, map_one]
    rw [sig_root] at h1
    calc sig c P h0 hr (rinv P) = (AdjoinRoot.root P * rinv P) * sig c P h0 hr (rinv P) := by
          rw [root_mul_rinv P h0, one_mul]
      _ = AdjoinRoot.root P * (rinv P * sig c P h0 hr (rinv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]
  have hext : (sig c P h0 hr).comp (sig c P h0 hr) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro e
      have := sig_alg h0 hr e
      rw [AdjoinRoot.algebraMap_eq] at this
      show sig c P h0 hr (sig c P h0 hr (AdjoinRoot.of P e)) = AdjoinRoot.of P e
      rw [this, ← AdjoinRoot.algebraMap_eq, sig_alg, hc]
    · show sig c P h0 hr (sig c P h0 hr (AdjoinRoot.root P)) = AdjoinRoot.root P
      rw [sig_root, hinv]
  exact congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) hext

theorem sig_root_mul_root (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) :
    sig c P h0 hr (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := by
  rw [sig_root, mul_comm, root_mul_rinv P h0]

end GlobalTheory.EllHermGlobal

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E]

theorem eq_zero_of_isNilpotent {P : E[X]} (hs : Squarefree P) (y : AdjoinRoot P) (hy : IsNilpotent y) : y = 0 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨m, hm⟩ := hy
  rw [← map_pow, AdjoinRoot.mk_eq_zero] at hm
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [pow_zero] at hm
    have h1 : (AdjoinRoot.mk P 1) = 0 := AdjoinRoot.mk_eq_zero.2 hm
    rw [map_one] at h1
    rw [← mul_one (AdjoinRoot.mk P f), h1, mul_zero]
  · exact AdjoinRoot.mk_eq_zero.2 ((hs.dvd_pow_iff_dvd h.ne').1 hm)

theorem trace_expand {A : Type} [CommRing A] [Algebra E A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι E A) (c : E →+* E) (σ : A →+* A)
    (hσ : ∀ e, σ (algebraMap E A e) = algebraMap E A (c e)) (x y : A) :
    Algebra.trace E A (σ x * y) = ∑ k, ∑ l, c (b.repr x k) * Algebra.trace E A (σ (b k) * b l) * b.repr y l := by
  have hsm : ∀ (e : E) (z : A), σ (e • z) = c e • σ z := by
    intro e z; rw [Algebra.smul_def, Algebra.smul_def, map_mul, hσ]
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, hsm, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.EllHermGlobal

noncomputable section

namespace GlobalTheory.EllHermGlobal

variable {E : Type} [Field E]

theorem exists_herm_of_selfRecip [CharZero E] (c : E →+* E) (hc : ∀ x, c (c x) = x) (P : E[X]) (hP : P.Monic)
    (hsep : P.Separable) (h0 : P.coeff 0 ≠ 0) (hr : C (c (P.coeff 0)) * P = (P.map c).reverse) :
    ∃ M G : Matrix (Fin P.natDegree) (Fin P.natDegree) E, M.charpoly = P ∧ IsUnit G ∧ cT c G = G ∧
      cT c M * G * M = G := by
  let A := AdjoinRoot P
  let pb := AdjoinRoot.powerBasis hP.ne_zero
  haveI : Module.Finite E A := pb.finite
  let b : Module.Basis (Fin P.natDegree) E A :=
    pb.basis.reindex (finCongr (AdjoinRoot.powerBasis_dim hP.ne_zero))
  let σ := sig c P h0 hr
  have hσ := sig_alg (c := c) h0 hr
  let M := Algebra.leftMulMatrix b (AdjoinRoot.root P)
  let G : Matrix (Fin P.natDegree) (Fin P.natDegree) E := fun i j => Algebra.trace E A (σ (b i) * b j)
  have hexp := trace_expand b c σ hσ
  refine ⟨M, G, ?_, ?_, ?_, ?_⟩
  · have h := charpoly_leftMulMatrix pb
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
      AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
    show (Algebra.leftMulMatrix b (AdjoinRoot.root P)).charpoly = P
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, h]
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    let y := b.equivFun.symm v
    have hy : ∀ l, b.repr y l = v l := fun l => by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    have htr : ∀ z : A, Algebra.trace E A (z * y) = 0 := by
      intro z
      rw [← sig_sig hc h0 hr z]
      rw [hexp]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp only [hy, mul_assoc, ← Finset.mul_sum]
      have := congrFun hv k
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [this, mul_zero]
    have hnil : IsNilpotent y :=
      GlobalTheory.UnitLemma.TraceNondeg.isNilpotent_of_trace_mul y fun z => by rw [mul_comm]; exact htr z
    have hy0 : y = 0 := eq_zero_of_isNilpotent hsep.squarefree y hnil
    apply hv0
    have : b.equivFun y = v := LinearEquiv.apply_symm_apply _ _
    rw [← this, hy0, map_zero]
  · ext i j
    show c (Algebra.trace E A (σ (b j) * b i)) = Algebra.trace E A (σ (b i) * b j)
    rw [← trace_semilinear b c hc σ (sig_sig hc h0 hr) hσ, map_mul, sig_sig hc h0 hr, mul_comm]
  · ext i j
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, M,
      Algebra.leftMulMatrix_eq_repr_mul]
    have hinv : G i j = Algebra.trace E A (σ (AdjoinRoot.root P * b i) * (AdjoinRoot.root P * b j)) := by
      have h1 : σ (AdjoinRoot.root P) * AdjoinRoot.root P = 1 := sig_root_mul_root h0 hr
      have e1 : σ (AdjoinRoot.root P * b i) = σ (AdjoinRoot.root P) * σ (b i) := map_mul σ _ _
      have e2 : σ (AdjoinRoot.root P * b i) * (AdjoinRoot.root P * b j) = σ (b i) * b j := by
        rw [e1]; linear_combination (σ (b i) * b j) * h1
      rw [e2]
    rw [hinv, hexp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]

end GlobalTheory.EllHermGlobal

namespace GlobalTheory.EllHermGlobal

theorem exists_charpoly_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := by
  intro E _ _ _ n P hP
  obtain ⟨h0, hr⟩ := GlobalTheory.ConjSelfRecip.ell_conj_selfRecip E n P hP
  obtain ⟨hm, hdeg, hsep, -⟩ := hP
  subst hdeg
  exact exists_herm_of_selfRecip (IsCMField.complexConj E).toRingEquiv.toRingHom
    (fun x => IsCMField.complexConj_apply_apply (K := E) x) P hm hsep h0 hr

end GlobalTheory.EllHermGlobal
end
end
end
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_form_char_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := by
  first | exact @GlobalTheory.EllHermGlobal.exists_charpoly_herm | exact GlobalTheory.EllHermGlobal.exists_charpoly_herm | (intros; apply GlobalTheory.EllHermGlobal.exists_charpoly_herm <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ExInertUnit

theorem globalForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ M G : Matrix (Fin n) (Fin n) E, M.charpoly = P ∧ IsUnit G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G := GlobalTheory.T.exists_hermitian_form_char_poly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eventually_mem_integers (a : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w n := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entries_of_mem_KGL {w : Pl E} {k : GLw n w} (hk : k ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    k.val i j ∈ w.adicCompletionIntegers E := by
  obtain ⟨a, rfl⟩ := hk
  exact (a.val i j).2

theorem mul_entries {w : Pl E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E) (hB : ∀ i j, B i j ∈ w.adicCompletionIntegers E)
    (i j : Fin n) : (A * B) i j ∈ w.adicCompletionIntegers E := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

set_option maxHeartbeats 800000 in

theorem local_step (hE : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (M G : Matrix (Fin n) (Fin n) E)
    (hG : IsUnit G) (hGh : cT (IsCMField.complexConj E).toRingEquiv.toRingHom G = G)
    (hMG : cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * G * M = G)
    (hM : ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E)
    (hG1 : ∀ i j, algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E)
    (hG2 : ∀ i j, algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E) :
    ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = M.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  obtain ⟨hconj, ⟨ϖ, q, hU, -⟩, -⟩ := hns hw
  let f := algebraMap E (w.adicCompletion E)
  let c := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcT : ∀ A : Matrix (Fin n) (Fin n) E, cT (cj w) (f.mapMatrix A) = f.mapMatrix (cT c A) := by
    intro A
    refine Matrix.ext fun i j => ?_
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact hconj _
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGu : IsUnit (f.mapMatrix G) := hG.map _
  have hginv : ((hGu.unit)⁻¹ : GLw n w).val = f.mapMatrix G⁻¹ := by
    have h : f.mapMatrix G⁻¹ * f.mapMatrix G = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
    exact Matrix.inv_eq_left_inv h
  have hgK : hGu.unit ∈ GlobalTheory.LFun.KGL w n :=
    mem_KGL_of_entries w _ (fun a b => by rw [IsUnit.unit_spec]; exact hG1 a b)
      (fun a b => by rw [hginv]; exact hG2 a b)
  have hgh : cT (cj w) hGu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, hcT, hGh]
  obtain ⟨k, hk, hkk⟩ := GlobalTheory.LFun.InertChart.exists_norm hU hgK hgh
  have hMu : IsUnit M := by
    have h : (G⁻¹ * cT c M * G) * M = 1 := by
      have h' := hMG
      simp only [Matrix.mul_assoc] at h' ⊢
      rw [h', Matrix.nonsing_inv_mul _ hdet]
    exact (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse h)
  have hMwu : IsUnit (f.mapMatrix M) := hMu.map _
  have hmG : cT (cj w) hMwu.unit.val * hGu.unit.val * hMwu.unit.val = hGu.unit.val := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, hcT, ← map_mul, ← map_mul, hMG]
  have hkinv : cT (cj w) (k⁻¹ : GLw n w).val * cT (cj w) k.val = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  set γ0 : GLw n w := k * hMwu.unit * k⁻¹ with hγ0
  have hγU : cT (cj w) γ0.val * 1 * γ0.val = 1 := by
    calc cT (cj w) γ0.val * 1 * γ0.val
        = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) hMwu.unit.val * (cT (cj w) k.val * k.val) * hMwu.unit.val)
            * (k⁻¹ : GLw n w).val := by
          rw [hγ0, Units.val_mul, Units.val_mul, cT_mul, cT_mul]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = cT (cj w) (k⁻¹ : GLw n w).val * (cT (cj w) k.val * k.val) * (k⁻¹ : GLw n w).val := by
          rw [hkk, hmG]
      _ = 1 := by
          simp only [← Matrix.mul_assoc]
          rw [hkinv, Matrix.one_mul, Units.mul_inv]
  have hγUL : γ0 ∈ UL n w := by
    rw [UL, if_neg hw]
    exact hγU
  refine ⟨⟨γ0, hγUL⟩, ?_, ?_⟩
  · rw [KL, Subgroup.mem_subgroupOf]
    have hinv : cT (cj w) γ0.val = (γ0⁻¹ : GLw n w).val := by
      rw [Matrix.coe_units_inv]
      exact (Matrix.inv_eq_left_inv (by simpa using hγU)).symm
    have hint : ∀ a b, γ0.val a b ∈ w.adicCompletionIntegers E := by
      intro a b
      rw [hγ0, Units.val_mul, Units.val_mul]
      refine mul_entries (mul_entries (entries_of_mem_KGL hk) (fun i j => ?_))
        (entries_of_mem_KGL (inv_mem hk)) a b
      rw [IsUnit.unit_spec]
      exact hM i j
    refine mem_KGL_of_entries w γ0 hint (fun a b => ?_)
    rw [← hinv]
    have h0 := hint b a
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h0 ⊢
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hv]
    exact h0
  · show (k.val * hMwu.unit.val * (k⁻¹ : GLw n w).val).charpoly = _
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj, IsUnit.unit_spec]
    exact Matrix.charpoly_map M f

theorem exists_integral_unitary_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  intro E _ _ _ hE n _ P hP
  obtain ⟨M, G, hMP, hG, hGh, hMG⟩ := globalForm E n P hP
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  have h3 : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (G⁻¹ i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_mem_integers _
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3 hw
  obtain ⟨γ, hγ, hc⟩ := local_step hE w hw M G hG hGh hMG hw1 hw2 hw3
  exact ⟨γ, hγ, by rw [hc, hMP]⟩

end GlobalTheory.ExInertUnit
end
end
