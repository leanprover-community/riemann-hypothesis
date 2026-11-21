import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwines

section
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem recursive_matrixPower_eq_matrix_pow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) :
    Matrix.of (Formalism.REAL.epow E k) = (Matrix.of E) ^ k := by
  induction k with
  | zero =>
    ext a b
    simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    ext a b
    rw [pow_succ, ← ih]
    simp [Formalism.REAL.epow, Matrix.mul_apply]

theorem scalarMatrix_mul_algebraMatrix_mul_apply {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((algebraMap ℂ A).mapMatrix P.transpose * M * (algebraMap ℂ A).mapMatrix Q.transpose) a b
      = ∑ c, ∑ d, (P c a * Q b d) • M c d := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]

theorem etr_conj_scalar_matrix {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL
  set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR
  have hLR : L * R = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]
  have hRL : R * L = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]
  have hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R := by
    ext a b
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]
    rfl
  have hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R := by
    intro m
    induction m with
    | zero => simp [hLR]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc L * Matrix.of E ^ m * R * (L * Matrix.of E * R)
          = L * Matrix.of E ^ m * (R * L) * Matrix.of E * R := by simp only [mul_assoc]
        _ = L * (Matrix.of E ^ m * Matrix.of E) * R := by rw [hRL]; simp only [mul_assoc, one_mul]
  have hk := recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k
  rw [hE, hpow, ← recursive_matrixPower_eq_matrix_pow] at hk
  have hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a
      = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d := by
    intro a
    have := congrFun (congrFun hk a) a
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply] at this
    exact this
  unfold Formalism.REAL.etr
  simp only [hent]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory
end

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  atlas_forward_decl GlobalTheory.etr_conj_scalar_matrix
end

section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_trace_power_cyclic_words : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ), Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  first | exact @GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord | exact GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord | (intros; apply GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord <;> assumption)
end

section
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem freeAlgebra_lift_eq_sum_monomials {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X) : FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  set e := (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ X ≃ₐ[ℂ] MonoidAlgebra ℂ (FreeMonoid X))
  have he : ∀ x : X, e (FreeAlgebra.ι ℂ x) = MonoidAlgebra.of ℂ (FreeMonoid X) (FreeMonoid.of x) := by
    intro x
    simp [e, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  have hF : ((FreeAlgebra.lift ℂ f).comp e.symm.toAlgHom) = MonoidAlgebra.lift ℂ B (FreeMonoid X) (FreeMonoid.lift f) := by
    rw [← (MonoidAlgebra.lift ℂ B (FreeMonoid X)).apply_symm_apply ((FreeAlgebra.lift ℂ f).comp e.symm.toAlgHom)]
    congr 1
    apply FreeMonoid.hom_eq
    intro x
    have hx : e.symm (MonoidAlgebra.of ℂ (FreeMonoid X) (FreeMonoid.of x)) = FreeAlgebra.ι ℂ x := by
      rw [← he x, e.symm_apply_apply]
    rw [MonoidAlgebra.of_apply] at hx
    rw [MonoidAlgebra.lift_symm_apply]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom, hx, FreeAlgebra.lift_ι_apply, FreeMonoid.lift_eval_of]
  have := AlgHom.congr_fun hF (e p)
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, MonoidAlgebra.lift_apply, FreeMonoid.lift_apply] at this
  exact this
end GlobalTheory
end

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeAlgebra_lift_monoid_sum : ∀ {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X), FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  atlas_forward_decl GlobalTheory.freeAlgebra_lift_eq_sum_monomials
end

section
section
open scoped InnerProductSpace

noncomputable section

open Matrix

namespace GlobalTheory.MatCoefDeriv

variable {n : ℕ} {ε : Fin n → Bool}

theorem exp_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet ε) (t : ℝ) :
    Formalism.REAL.inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := GlobalTheory.GKLie.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨_, _, hJJ, hJJ⟩, rfl⟩
  have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
  have hXh : Xᴴ = Formalism.REAL.Jm ε * (-X) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [hJinv]
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [h1, mul_neg, neg_mul]
  have hc : ((t : ℂ) • X)ᴴ = Formalism.REAL.Jm ε * (-((t : ℂ) • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [conjTranspose_smul, hXh, Complex.star_def, Complex.conj_ofReal]
    simp [smul_neg, mul_smul_comm, smul_mul_assoc]
  unfold Formalism.REAL.inUJ
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hu, hJinv]
  have hcomm : Commute (-((t : ℂ) • X)) ((t : ℂ) • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε *
        NormedSpace.exp ((t : ℂ) • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-((t : ℂ) • X)) * NormedSpace.exp ((t : ℂ) • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Rd_coef {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ)
    {u : H} (hu : Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u) (w : H)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : ∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet ε)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Rd X f g = ⟪w, ρ g (PI.PhMeasCore.dsig ρ X u)⟫_ℂ := by
  set γ : ℝ → H := fun t => ρ (NormedSpace.exp ((t : ℂ) • X)) u with hγ
  let L : H →L[ℝ] ℂ := ((innerSL ℂ w).comp (ρ g)).restrictScalars ℝ
  have hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) = fun t => L (γ t) := by
    funext t
    have he := exp_inUJ hX t
    rw [hf _ (by
      unfold Formalism.REAL.inUJ at hg he ⊢
      rw [conjTranspose_mul]
      calc _ = (NormedSpace.exp ((t : ℂ) • X))ᴴ * (gᴴ * Formalism.REAL.Jm ε * g) *
            NormedSpace.exp ((t : ℂ) • X) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg, he])]
    rw [hρ.2 g hg _ he]
    rfl
  have hdiff : DifferentiableAt ℝ γ 0 := by
    have h := GlobalTheory.GKLie.differentiableAt_orbit hu hX
    have e : γ = fun t : ℝ => ρ (NormedSpace.exp (t • X)) u := by
      funext t; simp only [hγ, Complex.coe_smul]
    rw [e]; exact h
  unfold Formalism.REAL.Rd
  rw [hfun]
  show deriv (⇑L ∘ γ) 0 = _
  rw [(L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdiff.hasDerivAt).deriv]
  rfl

theorem cpart1_eq (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z = (1 / 2 : ℂ) • (Z + PI.DSInfCharCap.thetaJ ε Z) := by
  simp [Formalism.REAL.cpart1, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]

theorem cpart2_eq (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart2 ε Z = (1 / (2 * Complex.I)) • (Z - PI.DSInfCharCap.thetaJ ε Z) := by
  simp [Formalism.REAL.cpart2, PI.DSInfCharCap.thetaJ, sub_eq_add_neg]

theorem Eab_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ →
    ∀ u : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u → ∀ (w : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ),
    (∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ) → ∀ (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ),
    Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b f g =
      ⟪w, ρ g (PI.DSInfCharCap.dsigC ε ρ (Matrix.single a b 1) u)⟫_ℂ := by
  intro n ε H _ _ ρ hρ u hu w f hf a b g hg
  have h1 := Rd_coef hρ hu w hf (GlobalTheory.GKLie.cre_mem (ε := ε) (Matrix.single a b 1)) hg
  have h2 := Rd_coef hρ hu w hf (GlobalTheory.GKLie.cim_mem (ε := ε) (Matrix.single a b 1)) hg
  unfold Formalism.REAL.Eab Formalism.REAL.Ec PI.DSInfCharCap.dsigC
  rw [cpart1_eq, cpart2_eq]
  unfold GlobalTheory.GKLie.cre at h1
  unfold GlobalTheory.GKLie.cim at h2
  rw [h1, h2, map_add, map_smul, inner_add_right, inner_smul_right]

end GlobalTheory.MatCoefDeriv
end
end

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_derivative_formula : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ u : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u → ∀ (w : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ) → ∀ (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b f g = ⟪w, ρ g (PI.DSInfCharCap.dsigC ε ρ (Matrix.single a b 1) u)⟫_ℂ := by
  atlas_forward_decl GlobalTheory.MatCoefDeriv.Eab_coef
end

section
noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.GKLie

theorem epow_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) : ∀ k a b, R * epow E k a b = epow E' k a b * R := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [Formalism.REAL.epow]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    simp only [Formalism.REAL.epow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc, ih, mul_assoc, h, ← mul_assoc]

theorem etr_intertwine {A : Type} [Ring A] {n : ℕ} (E E' : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, R * E a b = E' a b * R) (k : ℕ) : R * etr E k = etr E' k * R := by
  simp only [etr, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => epow_intertwine E E' R h k a a

theorem single_mul_single' {n : ℕ} (a b c d : Fin n) :
    (single a b (1 : ℂ)) * single c d 1 = if b = c then single a d 1 else 0 := by
  split_ifs with h
  · subst h; rw [single_mul_single_same, one_mul]
  · exact single_mul_single_of_ne _ _ _ _ h _

theorem conj_single {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    P * single a b 1 * P⁻¹ = ∑ c, ∑ d, (P c a * P⁻¹ b d) • single c d (1 : ℂ) := by
  ext i j
  simp [mul_apply, single_apply, Matrix.sum_apply, ite_and, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section Main

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem gAct_conj_glRel (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    GlRel (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) := by
  have hPi : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).1 hP)
  have hcb : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, P * X * P⁻¹ * (P * Y * P⁻¹) = P * (X * Y) * P⁻¹ := by
    intro X Y
    simp only [mul_assoc]
    rw [← mul_assoc P⁻¹ P, hPi, one_mul]
  intro a b c d
  simp only []
  rw [← gAct_bracket, hcb, hcb, ← sub_mul, ← mul_sub, single_mul_single', single_mul_single']
  split_ifs <;> simp [mul_sub, sub_mul]

theorem gAct_conj_sum (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) :
    (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) =
      fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • gAct hρ hV (single c d 1) := by
  funext a b
  rw [conj_single]
  simp only [map_sum, map_smul]

theorem gAct_conj_etr (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    etr (fun a b => gAct hρ hV (P * single a b 1 * P⁻¹)) k = etr (fun a b => gAct hρ hV (single a b 1)) k := by
  rw [gAct_conj_sum]
  exact GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix (fun a b => gAct hρ hV (single a b 1)) P hP k

theorem dsigCW_eq (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (l : List (Fin n × Fin n)) (v : kFinVec ε ρ) :
    PI.DSInfCharCap.dsigCW ε ρ (l.map PI.DSInfCharCap.unitM) v =
      (((l.map fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)).prod v : kFinVec ε ρ) : H) := by
  induction l with
  | nil => simp [PI.DSInfCharCap.dsigCW]
  | cons x l ih =>
    rw [List.map_cons, PI.DSInfCharCap.dsigCW.eq_2, ih, List.map_cons, List.prod_cons, Module.End.mul_apply,
      gAct_coe]
    rfl

theorem actU_eq (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ) :
    actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)) p v :
      kFinVec ε ρ) : H) := by
  rw [GlobalTheory.T.freeAlgebra_lift_monoid_sum]
  unfold PI.DSInfCharCap.actU
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dsigCW_eq hρ hV]

end Main

end GlobalTheory.GKLie

namespace GlobalTheory.GKLie

section KPart

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kset_facts {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) :
    κᴴ * κ = 1 ∧ κ⁻¹ = κᴴ ∧ κ * Jm ε = Jm ε * κ ∧ κᴴ * Jm ε = Jm ε * κᴴ := by
  obtain ⟨hu, hc⟩ := hκ
  have h1 : κᴴ * κ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff'] at hu
    simpa [Matrix.star_eq_conjTranspose] using hu
  refine ⟨h1, Matrix.inv_eq_left_inv h1, hc, ?_⟩
  have := congrArg conjTranspose hc
  simpa [conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem theta_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    PI.DSInfCharCap.thetaJ ε (κ * Y * κ⁻¹) = κ * PI.DSInfCharCap.thetaJ ε Y * κ⁻¹ := by
  obtain ⟨_, hinv, hc, hc'⟩ := kset_facts hκ
  rw [hinv]
  simp only [PI.DSInfCharCap.thetaJ, conjTranspose_mul, conjTranspose_conjTranspose, mul_neg, neg_mul, mul_assoc]
  rw [hc', ← mul_assoc (Jm ε) κ, ← hc, mul_assoc]

theorem cre_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cre ε (κ * Y * κ⁻¹) = κ * cre ε Y * κ⁻¹ := by
  unfold cre
  rw [theta_kconj hκ]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]

theorem cim_kconj {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    cim ε (κ * Y * κ⁻¹) = κ * cim ε Y * κ⁻¹ := by
  unfold cim
  rw [theta_kconj hκ]
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]

def kRes (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε) :
    Module.End ℂ (kFinVec ε ρ) :=
  (ρ κ : H →ₗ[ℂ] H).restrict (fun x hx => hV.kStable κ hκ x hx)

theorem kRes_coe (hV : IsGKSub ε ρ (kFinVec ε ρ)) (κ : Matrix (Fin n) (Fin n) ℂ) (hκ : κ ∈ Kset ε)
    (v : kFinVec ε ρ) : ((kRes hV κ hκ v : kFinVec ε ρ) : H) = ρ κ v := rfl

theorem gAct_kconj (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (Y : Matrix (Fin n) (Fin n) ℂ) :
    kRes hV κ hκ * gAct hρ hV Y = gAct hρ hV (κ * Y * κ⁻¹) * kRes hV κ hκ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, kRes_coe, gAct_coe, gAct_coe, kRes_coe, dsigC_eq, dsigC_eq,
    cre_kconj hκ, cim_kconj hκ,
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cre_mem Y) v (hV.smooth v v.2),
    GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H ρ hρ κ hκ _ (cim_mem Y) v (hV.smooth v v.2), map_add, map_smul]

theorem etr_kequiv (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ))
    {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ ∈ Kset ε) (k : ℕ) (v w : kFinVec ε ρ) (hw : (w : H) = ρ κ v) :
    ((etr (fun a b => gAct hρ hV (single a b 1)) k w : kFinVec ε ρ) : H) =
      ρ κ ((etr (fun a b => gAct hρ hV (single a b 1)) k v : kFinVec ε ρ) : H) := by
  have hw' : w = kRes hV κ hκ v := Subtype.ext (by rw [hw, kRes_coe])
  have hU : IsUnit κ := (isUnit_iff_isUnit_det κ).2 (isUnit_det_of_left_inverse (kset_facts hκ).1)
  have hint := etr_intertwine (fun a b => gAct hρ hV (single a b 1))
    (fun a b => gAct hρ hV (κ * single a b 1 * κ⁻¹)) (kRes hV κ hκ) (fun a b => gAct_kconj hρ hV hκ _) k
  rw [gAct_conj_etr hρ hV κ hU k] at hint
  rw [hw', ← kRes_coe hV κ hκ, ← Module.End.mul_apply, ← Module.End.mul_apply, hint]

theorem eword_coef (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (w' : H) :
    ∀ (l : List (Fin n × Fin n)) (u : kFinVec ε ρ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eword ε l (fun x => ⟪w', ρ x u⟫_ℂ) g =
        ⟪w', ρ g (((l.map fun ab : Fin n × Fin n => gAct hρ hV (single ab.1 ab.2 1)).prod u : kFinVec ε ρ) : H)⟫_ℂ := by
  intro l
  induction l with
  | nil => intro u g _; simp [Formalism.REAL.Eword]
  | cons p l ih =>
    intro u g hg
    rw [Formalism.REAL.Eword.eq_2]
    beta_reduce
    rw [GlobalTheory.T.matrix_coefficient_derivative_formula n ε H ρ hρ _ (hV.smooth _ ((l.map fun ab : Fin n × Fin n =>
      gAct hρ hV (single ab.1 ab.2 1)).prod u).2) w' _ (fun g' hg' => ih u g' hg') p.1 p.2 g hg]
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, gAct_coe]

theorem gelf_coef (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (w' : H) (m : ℕ)
    (v : kFinVec ε ρ) :
    GlobalTheory.Dec.gelf ε m (fun x => ⟪w', ρ x v⟫_ℂ) 1 =
      ⟪w', ((etr (fun a b => gAct hρ hV (single a b 1)) (m + 1) v : kFinVec ε ρ) : H)⟫_ℂ := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [Formalism.REAL.inUJ]
  unfold GlobalTheory.Dec.gelf
  rw [GlobalTheory.T.elementary_trace_power_cyclic_words]
  simp only [eword_coef hρ hV w' _ v 1 h1, hρ.1, ContinuousLinearMap.one_apply, LinearMap.sum_apply,
    Submodule.coe_sum, inner_sum]

theorem etr_infChar (hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ) (hV : IsGKSub ε ρ (kFinVec ε ρ)) (χ : Fin n → ℂ)
    (hχ : HasInfChar ε χ ρ) (k : ℕ) (v : kFinVec ε ρ) :
    etr (fun a b => gAct hρ hV (single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  set T := etr (fun a b => gAct hρ hV (single a b 1)) (k + 1) with hT
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [Formalism.REAL.inUJ]
  have key : ∀ w' : kFinVec ε ρ, ⟪(w' : H), (T v : H)⟫_ℂ = gelfVal χ (k + 1) * ⟪(w' : H), (v : H)⟫_ℂ := by
    intro w'
    have := (hχ v w' v.2 w'.2).2 k 1 h1
    rw [gelf_coef hρ hV] at this
    simpa [hρ.1] using this
  set z : kFinVec ε ρ := T v - gelfVal χ (k + 1) • v with hz
  have hzH : (z : H) = (T v : H) - gelfVal χ (k + 1) • (v : H) := by
    rw [hz, Submodule.coe_sub, Submodule.coe_smul]
  have hzz : ⟪(z : H), (z : H)⟫_ℂ = 0 := by
    conv_lhs => arg 3; rw [hzH]
    rw [inner_sub_right, inner_smul_right, key z, sub_self]
  have h0 : (z : H) = 0 := inner_self_eq_zero.1 hzz
  exact sub_eq_zero.1 (Subtype.ext h0)

end KPart

theorem kFin_glModule : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → IsGKSub ε ρ (kFinVec ε ρ) → ∃ A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε ρ), (∀ X ∈ lieSet ε, ∀ v, ((A X v : kFinVec ε ρ) : H) = dRep ρ X v) ∧ (∀ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P → GlRel (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) ∧ ∀ k : ℕ, etr (fun a b => A (P * Matrix.single a b 1 * P⁻¹)) k = etr (fun a b => A (Matrix.single a b 1)) k) ∧ (∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : kFinVec ε ρ), actU ε ρ p (v : H) = ((FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => A (Matrix.single ab.1 ab.2 1)) p v : kFinVec ε ρ) : H)) ∧ (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((etr (fun a b => A (Matrix.single a b 1)) k w : kFinVec ε ρ) : H) = ρ κ ((etr (fun a b => A (Matrix.single a b 1)) k v : kFinVec ε ρ) : H)) ∧ ∀ χ : Fin n → ℂ, HasInfChar ε χ ρ → ∀ (k : ℕ) v, etr (fun a b => A (Matrix.single a b 1)) (k + 1) v = gelfVal χ (k + 1) • v := by
  intro n ε H _ _ _ ρ hadm hV
  have hρ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) ρ := hadm.1
  exact ⟨gAct hρ hV, fun X hX v => gAct_of_mem hρ hV hX v,
    fun P hP => ⟨gAct_conj_glRel hρ hV P hP, gAct_conj_etr hρ hV P hP⟩, fun p v => actU_eq hρ hV p v,
    fun κ hκ k v w hw => etr_kequiv hρ hV hκ k v w hw, fun χ hχ k v => etr_infChar hρ hV χ hχ k v⟩

end GlobalTheory.GKLie
end
end
