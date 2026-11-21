import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CoefDiff
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.SubMat

section
open Matrix UpperTheory.V.Weyl

private theorem pre_coef_differentiableAt {n : ℕ} (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) :
    DifferentiableAt ℂ (Ξ.coef i j) x := by
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun y => MvPolynomial.aeval (fun ab : Fin n × Fin n => y ab.1 ab.2) p := by
    funext y
    simp [Pre.coef, hp, MvPolynomial.coe_aeval_eq_eval]
  rw [h]
  exact (AnalyticAt.aeval_mvPolynomial (fun ab : Fin n × Fin n =>
    (((ContinuousLinearMap.proj ab.2 : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj ab.1 : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).analyticAt x)) p).differentiableAt

private theorem hasDerivAt_pre_mat_one_add_smul {n : ℕ} (Ξ : Pre n) (X : Matrix (Fin n) (Fin n) ℂ) (k j : Fin Ξ.d) :
    HasDerivAt (fun t : ℂ => Ξ.mat (of (oneM n + t • of.symm X)) k j) (Ξ.D X k j) 0 := by
  have hc : HasDerivAt (fun t : ℂ => oneM n + t • of.symm X) (of.symm X) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).smul_const (of.symm X)).const_add (oneM n)
  have hf := (pre_coef_differentiableAt Ξ k j (oneM n + (0:ℂ) • of.symm X)).hasFDerivAt.comp_hasDerivAt (0:ℂ) hc
  simp only [zero_smul, add_zero] at hf
  exact hf

theorem UpperTheory.V.Weyl.adEq :
    ∀ (n : ℕ) (Ξ : Pre n) (P Z W : Matrix (Fin n) (Fin n) ℂ), P * Z = W * P → Ξ.mat P * Ξ.D Z = Ξ.D W * Ξ.mat P := by
  intro n Ξ P Z W h
  have key : ∀ t : ℂ, P * of (oneM n + t • of.symm Z) = of (oneM n + t • of.symm W) * P := by
    intro t
    change P * (1 + t • Z) = (1 + t • W) * P
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h, mul_one, one_mul]
  ext i j
  have hZ : HasDerivAt (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j)
      ((Ξ.mat P * Ξ.D Z) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ Z k j).const_mul _
  have hW : HasDerivAt (fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j)
      ((Ξ.D W * Ξ.mat P) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ W i k).mul_const _
  have hfun : (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j) =
      fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j := by
    funext t
    rw [← map_mul, ← map_mul, key]
  rw [hfun] at hZ
  exact hZ.unique hW
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, Q t * P t = 1) ∧
      ∀ i j, HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧ HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef
    have hE : E * E = E := by
      rw [hEdef, Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1)
          + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by
          rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j
      constructor
      · have h := (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by
          simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        have h := ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef
    have hE : E * E = 0 := by
      rw [hEdef]
      simp [Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]
      abel
    · intro i j
      constructor
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
end

section
open Matrix UpperTheory.V.Weyl

private theorem hasDerivAt_mul_mul_entry {n : ℕ} (P Q : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (P' Q' Y : Matrix (Fin n) (Fin n) ℂ)
    (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0)
    (hQ : ∀ i j, HasDerivAt (fun t => Q t i j) (Q' i j) 0) (p q : Fin n) :
    HasDerivAt (fun t => (P t * Y * Q t) p q) ((P' * Y * Q 0 + P 0 * Y * Q') p q) 0 := by
  have h : HasDerivAt (fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q)
      (∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q)) 0 :=
    HasDerivAt.fun_sum fun m _ =>
      (HasDerivAt.fun_sum fun l _ => (hP p l).mul_const (Y l m)).mul (hQ m q)
  have e : (P' * Y * Q 0 + P 0 * Y * Q') p q =
      ∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simp only [Matrix.mul_apply]
  have ef : (fun t => (P t * Y * Q t) p q) = fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q := by
    funext t
    simp only [Matrix.mul_apply]
  rw [e, ef]
  exact h

private theorem pre_D_eq_sum_single {n : ℕ} (Ξ : Pre n) (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin Ξ.d) :
    Ξ.D M i k = ∑ p, ∑ q, M p q * Ξ.D (Matrix.single p q 1) i k := by
  have hM : M = ∑ p, ∑ q, M p q • Matrix.single p q (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [hM]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem UpperTheory.V.Weyl.bracket :
    ∀ (n : ℕ) (Ξ : Pre n) (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ),
      Ξ.E a b * Ξ.D Y - Ξ.D Y * Ξ.E a b = Ξ.D (Matrix.single a b 1 * Y - Y * Matrix.single a b 1) := by
  intro n Ξ a b Y
  obtain ⟨P, Q, hP0, hQ0, hQP, hd⟩ := invCurve n a b
  set s : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hs
  set c : Matrix (Fin n) (Fin n) ℂ := s * Y - Y * s with hc
  have hE : ∀ t, Ξ.mat (P t) * Ξ.D Y = Ξ.D (P t * Y * Q t) * Ξ.mat (P t) := fun t =>
    adEq n Ξ (P t) Y (P t * Y * Q t) (by rw [Matrix.mul_assoc (P t * Y), hQP t, Matrix.mul_one])
  have hmat := curve n Ξ P s hP0 (fun i j => (hd i j).1)
  have hM : ∀ p q, HasDerivAt (fun t => (P t * Y * Q t) p q) (c p q) 0 := by
    intro p q
    have h := hasDerivAt_mul_mul_entry P Q s (-s) Y
      (fun i j => (hd i j).1) (fun i j => by simpa using (hd i j).2) p q
    simpa [hP0, hQ0, hc, sub_eq_add_neg, Matrix.mul_neg] using h
  have hdD : ∀ i k, HasDerivAt (fun t => Ξ.D (P t * Y * Q t) i k) (Ξ.D c i k) 0 := by
    intro i k
    have h : HasDerivAt (fun t => ∑ p, ∑ q, (P t * Y * Q t) p q * Ξ.D (Matrix.single p q 1) i k)
        (∑ p, ∑ q, c p q * Ξ.D (Matrix.single p q 1) i k) 0 :=
      HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ => (hM p q).mul_const _
    rw [pre_D_eq_sum_single Ξ c i k]
    convert h using 1
    funext t
    exact pre_D_eq_sum_single Ξ _ i k
  ext i j
  have hL : HasDerivAt (fun t => (Ξ.mat (P t) * Ξ.D Y) i j)
      (∑ k, Ξ.D s i k * Ξ.D Y k j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hmat i k).mul_const _
  have hR : HasDerivAt (fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j)
      (∑ k, (Ξ.D c i k * Ξ.mat (P 0) k j + Ξ.D (P 0 * Y * Q 0) i k * Ξ.D s k j)) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hdD i k).mul (hmat k j)
  have hfun : (fun t => (Ξ.mat (P t) * Ξ.D Y) i j) =
      fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j :=
    funext fun t => by rw [hE t]
  rw [hfun] at hL
  have hu := hL.unique hR
  simp only [hP0, hQ0, Matrix.mul_one, Matrix.one_mul, map_one, Finset.sum_add_distrib] at hu
  simp only [Matrix.sub_apply, Pre.E, Matrix.mul_apply]
  rw [hu]
  simp [Matrix.one_apply, s]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.glRel :
    ∀ (n : ℕ) (Ξ : Pre n), Formalism.REAL.GlRel Ξ.E := by
  intro n Ξ a b c d
  have h := UpperTheory.V.Weyl.bracket n Ξ a b (Matrix.single c d 1)
  have h1 : Ξ.D (Matrix.single a b (1:ℂ) * Matrix.single c d 1) = if b = c then Ξ.E a d else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  have h2 : Ξ.D (Matrix.single c d (1:ℂ) * Matrix.single a b 1) = if d = a then Ξ.E c b else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  rw [map_sub, h1, h2] at h
  exact h
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.qdetComm :
    ∀ (n : ℕ) (Ξ : Pre n) (u : ℂ) (y : Matrix (Fin n) (Fin n) ℂ), IsUnit y →
      Ξ.mat y * Formalism.REAL.qdet Ξ.E u = Formalism.REAL.qdet Ξ.E u * Ξ.mat y := by
  intro n Ξ u y hy
  obtain ⟨Q, hQ⟩ := hy.exists_left_inv
  have hW : ∀ a b : Fin n, y * Matrix.single a b (1 : ℂ) * Q =
      ∑ c, ∑ d, (y c a * Q b d) • Matrix.single c d (1 : ℂ) := by
    intro a b
    rw [Matrix.matrix_eq_sum_single (y * Matrix.single a b (1 : ℂ) * Q)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_single]
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  have h : ∀ a b : Fin n, Ξ.mat y * Ξ.E a b =
      (∑ c, ∑ d, (y c a * Q b d) • Ξ.E c d) * Ξ.mat y := by
    intro a b
    have h1 := UpperTheory.V.Weyl.adEq n Ξ y (Matrix.single a b 1) (y * Matrix.single a b (1 : ℂ) * Q)
      (by rw [mul_assoc, hQ, mul_one])
    rw [hW] at h1
    simp only [map_sum, map_smul] at h1
    exact h1
  rw [GlobalTheory.CapAdInv.qdet_semiconj _ _ _ h u,
    GlobalTheory.CapAdInv.qdet_ad _ (UpperTheory.V.Weyl.glRel n Ξ) y Q hQ u]
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.commAll :
    ∀ (n : ℕ) (Ξ : Pre n) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), (∀ y, IsUnit y → Ξ.mat y * Z = Z * Ξ.mat y) →
      ∀ y, Ξ.mat y * Z = Z * Ξ.mat y := by
  intro n Ξ Z hZ y
  choose P hP using Ξ.poly
  let Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ := fun i j =>
    ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j
  have hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j,
      (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j) := by
    intro g i j
    simp [Q, Matrix.mul_apply, hP, map_sum, mul_comm]
  rw [← sub_eq_zero]
  ext i j
  rw [hent, Matrix.zero_apply]
  have hQ : Q i j = 0 := MvPolynomial.eq_of_eval_eq_on_gl (fun g => by
    rw [← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply, map_zero])
  rw [hQ, map_zero]
end

section
open Matrix UpperTheory.V.Weyl

private theorem UpperTheory.V.Weyl.top_weight_lie_action (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ)
    (h : Ξ.IsTop ν v) (a b : Fin n) (hab : a ≤ b) (f : ℂ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (hfe : ∀ t : ℂ, ∏ k, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • single a b (1 : ℂ)) k k ^ ν k = f t) :
    Ξ.E a b *ᵥ v = f' • v := by
  have hc := UpperTheory.V.Weyl.curve n Ξ (fun t => 1 + t • single a b (1 : ℂ)) (single a b 1) (by simp) (by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (single a b (1 : ℂ) i j)).const_add
      ((1 : Matrix (Fin n) (Fin n) ℂ) i j))
  funext i
  have h1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) ((Ξ.E a b *ᵥ v) i) 0 := by
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hc i j).mul_const (v j)
  have h2 : (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) = fun t => f t * v i := by
    funext t
    rw [h _ ?_, hfe]
    · rfl
    · intro p q hpq
      have : ¬ (a = p ∧ b = q) := by
        rintro ⟨rfl, rfl⟩
        exact absurd hab (not_le.mpr hpq)
      simp [Matrix.one_apply_ne hpq.ne', Matrix.single_apply, this]
  rw [h2] at h1
  exact h1.unique (hf.mul_const (v i))

theorem UpperTheory.V.Weyl.topLie :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), Ξ.IsTop ν v →
      (∀ a, Ξ.E a a *ᵥ v = (ν a : ℂ) • v) ∧ ∀ a b, a < b → Ξ.E a b *ᵥ v = 0 := by
  intro n Ξ ν v h
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a a le_rfl (fun t => (1 + t) ^ ν a) _ ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_pow (ν a)
    · intro t
      rw [Finset.prod_eq_single a]
      · simp
      · intro k _ hk
        simp [Matrix.single_apply, hk.symm]
      · simp
  · have := UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a b hab.le (fun _ => 1) 0 (hasDerivAt_const _ _) (by
      intro t
      refine Finset.prod_eq_one fun k _ => ?_
      have : ¬ (a = k ∧ b = k) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [Matrix.single_apply, this])
    simpa using this
end

section
open Matrix UpperTheory.V.Weyl

open Formalism.REAL in
private theorem UpperTheory.V.Weyl.map_quantum_determinant {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : φ (qdet X u) = qdet (fun a b => φ (X a b)) u := by
  have hT : ∀ v a b, φ (Tm X v a b) = Tm (fun a b => φ (X a b)) v a b := fun v a b => by
    unfold Tm
    split_ifs <;> simp
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, hT]

theorem UpperTheory.V.Weyl.qdetHW :
    ∀ (n d : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (ν : Fin n → ℂ) (v : Fin d → ℂ), Formalism.REAL.GlRel E →
      (∀ a, E a a *ᵥ v = ν a • v) → (∀ a b, a < b → E a b *ᵥ v = 0) →
      ∀ u : ℂ, Formalism.REAL.qdet E u *ᵥ v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v := by
  intro n d E ν v hgl h1 h2 u
  let φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (Fin d → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have hφ : ∀ M w, φ M w = M *ᵥ w := fun M w => Matrix.toLinAlgEquiv'_apply M w
  have hgl' : Formalism.REAL.GlRel (fun a b => φ (E a b)) := by
    intro a b c e
    have := congrArg φ (hgl a b c e)
    simpa only [map_sub, map_mul, apply_ite φ, map_zero] using this
  have hw : Formalism.REAL.IsHW (fun a b => φ (E a b)) ν v :=
    ⟨fun a => (hφ _ _).trans (h1 a), fun a b hab => (hφ _ _).trans (h2 a b hab)⟩
  rw [← hφ, UpperTheory.V.Weyl.map_quantum_determinant]
  exact Formalism.REAL.qDetHW _ n _ ν v hgl' hw u
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.preSub :
    ∀ (n : ℕ) (Ξ : Pre n) (S : Submodule ℂ (Fin Ξ.d → ℂ)), (∀ y, ∀ v ∈ S, Ξ.mat y *ᵥ v ∈ S) →
      ∃ (Ξ' : Pre n) (A : Matrix (Fin Ξ.d) (Fin Ξ'.d) ℂ) (B : Matrix (Fin Ξ'.d) (Fin Ξ.d) ℂ),
        Ξ'.d = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ ∀ X, Ξ.D X * A = A * Ξ'.D X := by
  intro n Ξ S hS
  obtain ⟨d', A, B, ρ', hd, hBA, hA, hρ, hcomm⟩ :=
    UpperTheory.V.Weyl.subMat (Matrix (Fin n) (Fin n) ℂ) Ξ.d Ξ.mat S hS
  have hpoly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g,
      ρ' g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    choose p hp using Ξ.poly
    intro i j
    refine ⟨∑ l, (∑ k, MvPolynomial.C (B i k) * p k l) * MvPolynomial.C (A l j), fun g => ?_⟩
    rw [hρ]
    simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hp]
  let Ξ' : Pre n := ⟨d', ρ', hpoly⟩
  refine ⟨Ξ', A, B, hd, hBA, hA, fun X => ?_⟩
  have h0 : (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) 0 = 1 := by simp
  have hc : ∀ a b, HasDerivAt (fun t : ℂ => ((1 : Matrix (Fin n) (Fin n) ℂ) + t • X) a b) (X a b) 0 := by
    intro a b
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X a b)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
  have h1 := UpperTheory.V.Weyl.curve n Ξ _ X h0 hc
  have h2 := UpperTheory.V.Weyl.curve n Ξ' _ X h0 hc
  ext i j
  have e1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • X) * A) i j) ((Ξ.D X * A) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h1 i k).mul_const (A k j)
  have e2 : HasDerivAt (fun t : ℂ => (A * ρ' (1 + t • X)) i j) ((A * Ξ'.D X) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (h2 k j).const_mul (A i k)
  simp only [hcomm] at e1
  exact e1.unique e2
end

section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.scalar :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), v ≠ 0 → Ξ.IsTop ν v →
      ∃ Ξ' : Pre n, 0 < Ξ'.d ∧ Ξ'.d ≤ Ξ.d ∧ Ξ'.HasWt fun k => (ν k : ℂ) := by
  intro n Ξ ν v hv htop
  let S : Submodule ℂ (Fin Ξ.d → ℂ) :=
    Submodule.span ℂ (Set.range fun y : Matrix (Fin n) (Fin n) ℂ => Ξ.mat y *ᵥ v)
  have hS : ∀ y, ∀ w ∈ S, Ξ.mat y *ᵥ w ∈ S := by
    intro y w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [Matrix.mulVec_mulVec, ← map_mul]
      exact Submodule.subset_span ⟨y * z, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
      rw [Matrix.mulVec_add]
      exact S.add_mem hx hz
    | smul a x _ hx =>
      rw [Matrix.mulVec_smul]
      exact S.smul_mem a hx
  have hvS : v ∈ S := by
    have h : Ξ.mat 1 *ᵥ v ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using h
  obtain ⟨Ξ', A, B, hd, hBA, hA, hD⟩ := preSub n Ξ S hS
  obtain ⟨hdiag, hup⟩ := topLie n Ξ ν v htop
  refine ⟨Ξ', ?_, ?_, fun u => ?_⟩
  · rw [hd]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, hvS⟩, fun h => hv (congrArg Subtype.val h)⟩
  · rw [hd]
    simpa using Submodule.finrank_le S
  · set c : ℂ := ∏ k : Fin n, (u - ((k : ℕ) : ℂ) + (ν k : ℂ)) with hc
    have hQv : Formalism.REAL.qdet Ξ.E u *ᵥ v = c • v :=
      qdetHW n Ξ.d Ξ.E (fun k => (ν k : ℂ)) v (glRel n Ξ) hdiag hup u
    have hcomm : ∀ y, Ξ.mat y * Formalism.REAL.qdet Ξ.E u = Formalism.REAL.qdet Ξ.E u * Ξ.mat y :=
      commAll n Ξ _ (fun y hy => qdetComm n Ξ u y hy)
    have hQS : ∀ w ∈ S, Formalism.REAL.qdet Ξ.E u *ᵥ w = c • w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [Matrix.mulVec_mulVec, ← hcomm y, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_smul]
      | zero => simp
      | add x z _ _ hx hz => rw [Matrix.mulVec_add, hx, hz, smul_add]
      | smul a x _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
    have hR := qdetRect n Ξ.d Ξ'.d Ξ.E Ξ'.E A (fun a b => hD _) u
    have hcA : Formalism.REAL.qdet Ξ.E u * A = c • A := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hQS _ (hA w), Matrix.smul_mulVec]
    show Formalism.REAL.qdet Ξ'.E u = c • 1
    calc Formalism.REAL.qdet Ξ'.E u = (B * A) * Formalism.REAL.qdet Ξ'.E u := by rw [hBA, Matrix.one_mul]
      _ = B * (Formalism.REAL.qdet Ξ.E u * A) := by rw [Matrix.mul_assoc, hR]
      _ = c • 1 := by rw [hcA, Matrix.mul_smul, hBA]
end
