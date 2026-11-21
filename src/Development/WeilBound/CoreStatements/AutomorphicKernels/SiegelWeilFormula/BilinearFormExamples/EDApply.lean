import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.MapCAMul
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible

section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def BfE (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) : LinearMap.BilinForm F (Matrix (Fin m) (Fin n) E) :=
  LinearMap.mk₂ F (fun x z => Algebra.trace F E (xᵀ * J * z.map σ).trace)
    (fun x x' z => by simp [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x z => by simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun x z z' => by simp [Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.trace_add])
    (fun c x z => by
      have : (c • z).map σ = c • z.map σ := by ext i j; exact σ.toLinearMap.map_smul c (z i j)
      simp [this, Matrix.mul_smul, Matrix.trace_smul])

theorem BfE_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (x z : Matrix (Fin m) (Fin n) E) :
    BfE σ J x z = Algebra.trace F E (xᵀ * J * z.map σ).trace := rfl

theorem BfE_nondeg [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) : (BfE (n := n) σ J).Nondegenerate := by
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hdetT : IsUnit Jᵀ.det := by
    rw [Matrix.det_transpose]
    exact hdet
  have htr1 : Algebra.trace F E 1 ≠ 0 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap]
    simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
    exact Module.finrank_pos.ne'
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · by_contra hne
    have hy : Jᵀ * x ≠ 0 := by
      intro h0
      apply hne
      have h2 := congrArg (fun M => (Jᵀ)⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetT] using h2
    obtain ⟨b0, j0, hb⟩ : ∃ b j, (Jᵀ * x) b j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (Matrix.ext h)
    have h1 := hx ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ)
    have hσσ : ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ).map σ =
        Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹ := by
      ext a b
      simp only [Matrix.map_apply]
      exact hσ _
    have hswap : (xᵀ * J) j0 b0 = (Jᵀ * x) b0 j0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hv : (xᵀ * J * Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).trace = 1 := by
      rw [Matrix.trace_mul_single, hswap, op_smul_eq_mul, mul_inv_cancel₀ hb]
    rw [BfE_apply, hσσ, hv] at h1
    exact htr1 h1
  · by_contra hne
    have hw : J * z.map σ ≠ 0 := by
      intro h0
      apply hne
      have hz0 : z.map σ = 0 := by
        have h2 := congrArg (fun M => J⁻¹ * M) h0
        simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet] using h2
      ext a b
      have := congrFun (congrFun hz0 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      rw [Matrix.zero_apply, ← hσ (z a b), this, map_zero]
    obtain ⟨a0, b0, hb⟩ : ∃ a b, (J * z.map σ) a b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (Matrix.ext h)
    have h1 := hz (Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)
    have hv : ((Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)ᵀ * J * z.map σ).trace = 1 := by
      rw [Matrix.mul_assoc, Matrix.transpose_single, Matrix.trace_single_mul]
      simp [inv_mul_cancel₀ hb, mul_inv_cancel₀ hb]
    rw [BfE_apply, hv] at h1
    exact htr1 h1

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

theorem trace_int_mul (u : ℤ) (t : AE F E) :
    Algebra.trace (AF F) (AE F E) ((u : AE F E) * t) = (u : AF F) * Algebra.trace (AF F) (AE F E) t := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem trace_map_cA {σ : E →ₐ[F] E} {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) :
    (M.map (cA σ)).trace = cA σ M.trace := by
  simp [Matrix.trace, map_sum]

theorem Bf_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E) (u : ℤ)
    (hJ : ∀ i j, σ (J j i) = (u : E) * J i j) (X Z : Mx F E m n) :
    Bf σ J X Z = (u : AF F) * Bf σ J Z X := by
  have hJc : (incM F J).map (cA σ) = ((u : ℤ) : AE F E) • (incM F J)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    change cA σ (inclR (F := F) (AF F) (J i j)) = _ * inclR (F := F) (AF F) (J j i)
    rw [show cA σ (inclR (F := F) (AF F) (J i j)) = inclR (F := F) (AF F) (σ (J i j)) from rfl, hJ j i, map_mul, map_intCast]
  have hcc : (Z.map (cA σ)).map (cA σ) = Z := by ext i j; exact cA_cA hσ _
  unfold Bf
  rw [← trace_cA hσ, ← trace_map_cA, map_cA_mul, map_cA_mul, Matrix.transpose_map, hJc, hcc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_int_mul]
  congr 2
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem mapS_mul {σ : E →ₐ[F] E} {a b c : Type} [Fintype b] (x : Matrix a b E) (y : Matrix b c E) :
    (x * y).map σ = x.map σ * y.map σ := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem congr_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {ι : Type} [Fintype ι] (D b : Matrix ι ι E) (u : ℤ)
    (hD : Dᵀ.map σ = (u : E) • D) : ((bᵀ * D * b.map σ).map σ)ᵀ = (u : E) • (bᵀ * D * b.map σ) := by
  have hbb : (b.map σ).map σ = b := by ext i j; simp [hσ]
  rw [mapS_mul, mapS_mul, hbb, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.transpose_map,
    ← Matrix.transpose_map, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

theorem eps_eq {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (YJ : Matrix (Fin n) (Fin n) E) (u : ℤ)
    (hY : ∀ i j, σ (YJ j i) = (u : E) * YJ i j) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε) (hn : 1 ≤ n) : (ε : ℤ) = u := by
  have hD : (dbl YJ)ᵀ.map σ = (u : E) • dbl YJ := by
    ext (i | i) (j | j) <;> simp [dbl, hY]
  have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩))
    (congr_symm hσ (dbl YJ) b.1 u hD)
  simp only [hb] at h
  simp [jeps] at h
  exact_mod_cast h

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def Gm (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) :
    Matrix (Fin m × Fin n × Fin 2) (Fin m × Fin n × Fin 2) F :=
  LinearMap.BilinForm.toMatrix (bs.matrix (Fin m) (Fin n)) (BfE σ J)

theorem Gm_det [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) (bs : Module.Basis (Fin 2) F E) : (Gm (n := n) σ J bs).det ≠ 0 :=
  (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).1 (BfE_nondeg σ hσ J hJ)

theorem Bf_Ek_Ek [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (k k' : Fin m × Fin n × Fin 2) : Bf σ J (Ek bs k) (Ek bs k') = algebraMap F (AF F) (Gm σ J bs k k') := by
  obtain ⟨i, j, l⟩ := k
  obtain ⟨i', j', l'⟩ := k'
  have hE : ∀ (a : Fin m) (b : Fin n) (c : Fin 2), Ek bs (a, b, c) = incM F (Matrix.single a b (bs c)) := by
    intro a b c
    ext x y
    by_cases hx : a = x <;> by_cases hy : b = y <;> simp [Ek, incM, Matrix.single_apply, inclR, hx, hy]
  have hc : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M).map (cA σ) = incM F (M.map σ) := by
    intro M
    ext x y
    simp [incM, cA, inclR]
  have htr : ∀ M : Matrix (Fin m) (Fin n) E, (incM F M)ᵀ = incM F Mᵀ := by
    intro M
    ext x y
    rfl
  have ht : ∀ M : Matrix (Fin n) (Fin n) E, (incM F M).trace = inclR (F := F) (E := E) (AF F) M.trace := by
    intro M
    rw [incM, AddMonoidHom.map_trace]
  rw [Gm, LinearMap.BilinForm.toMatrix_apply, Module.Basis.matrix_apply, Module.Basis.matrix_apply, Bf, hE, hE, hc,
    htr, ← incM_mul, ← incM_mul, ht, trace_inclR']
  rfl

def bM (bs : Module.Basis (Fin 2) F E) : Module.Basis (Fin m × Fin n × Fin 2) (AF F) (Mx F E m n) :=
  (Algebra.TensorProduct.basis (AF F) bs).matrix (Fin m) (Fin n)


theorem bM_repr (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) (k : Fin m × Fin n × Fin 2) :
    (bM bs).repr X k = crdB bs X k := by
  obtain ⟨i, j, l⟩ := k
  have hinj : Function.Injective (Prod.map id ⇑(Equiv.sigmaEquivProd (Fin n) (Fin 2)) ∘
      ⇑(Equiv.sigmaEquivProd (Fin m) (Σ _ : Fin n, Fin 2))) :=
    (Function.injective_id.prodMap (Equiv.injective _)).comp (Equiv.injective _)
  simp [bM, Module.Basis.matrix, crdB, Pi.basis_repr]
  rw [show ((i, j, l) : Fin m × Fin n × Fin 2) = (Prod.map id ⇑(Equiv.sigmaEquivProd (Fin n) (Fin 2)) ∘
      ⇑(Equiv.sigmaEquivProd (Fin m) (Σ _ : Fin n, Fin 2))) ⟨i, ⟨j, l⟩⟩ from rfl,
    Finsupp.mapDomain_apply hinj, Pi.basis_repr, Pi.basis_repr]
  rfl

theorem incM_one {ι : Type} [Fintype ι] [DecidableEq ι] : incM F (1 : Matrix ι ι E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def eQ (b : GL (Fin n ⊕ Fin n) E) : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) ≃ₗ[AF F] Mx F E m n × Mx F E m n :=
  LinearEquiv.ofLinear
    { toFun := fun w => ((w * (incM F (b⁻¹).1)ᵀ).toCols₁, (w * (incM F (b⁻¹).1)ᵀ).toCols₂)
      map_add' := fun w w' => by rw [Matrix.add_mul]; rfl
      map_smul' := fun c w => by rw [Matrix.smul_mul]; rfl }
    { toFun := fun p => p.1 * (incM F b.1.toCols₁)ᵀ + p.2 * (incM F b.1.toCols₂)ᵀ
      map_add' := fun p p' => by simp [Matrix.add_mul]; abel
      map_smul' := fun c p => by simp [Matrix.smul_mul, smul_add] }
    (by
      refine LinearMap.ext fun p => ?_
      obtain ⟨Z, X⟩ := p
      have h1 : (incM F b.1)ᵀ * (incM F (b⁻¹).1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.inv_mul, incM_one, Matrix.transpose_one]
      show (((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₁,
        ((Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) * (incM F (b⁻¹).1)ᵀ).toCols₂) = (Z, X)
      rw [show Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ = Matrix.fromCols Z X * (incM F b.1)ᵀ by
        rw [incM_b, Matrix.fromCols_mul_fromRows], Matrix.mul_assoc, h1, Matrix.mul_one]
      simp)
    (by
      refine LinearMap.ext fun w => ?_
      have h1 : (incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, ← incM_mul, Units.mul_inv, incM_one, Matrix.transpose_one]
      show (w * (incM F (b⁻¹).1)ᵀ).toCols₁ * (incM F b.1.toCols₁)ᵀ + (w * (incM F (b⁻¹).1)ᵀ).toCols₂ * (incM F b.1.toCols₂)ᵀ = w
      rw [← Matrix.fromCols_mul_fromRows, ← incM_b, Matrix.fromCols_toCols, Matrix.mul_assoc, h1, Matrix.mul_one])

theorem eQ_symm_apply (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    (eQ b).symm (Z, X) = Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ := rfl

theorem eQ_frame (b : GL (Fin n ⊕ Fin n) E) (Z X : Mx F E m n) :
    eQ b (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (Z, X) := by
  rw [← eQ_symm_apply, LinearEquiv.apply_symm_apply]

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def Pm (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) :
    Matrix (Fin m × Fin n × Fin 2) (Fin m × Fin n × Fin 2) (AF F) :=
  ((Gm (n := n) σ J bs).map (algebraMap F (AF F)))ᵀ

theorem Pm_unit [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) (bs : Module.Basis (Fin 2) F E) : IsUnit (Pm (n := n) σ J bs).det := by
  rw [Pm, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Ne.isUnit (Gm_det σ hσ J hJ bs)).map _

def eD (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (b : GL (Fin n ⊕ Fin n) E)
    (hP : IsUnit (Pm (n := n) σ J bs).det) :
    Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) ≃ₗ[AF F] (Fin m × Fin n × Fin 2 → AF F) × (Fin m × Fin n × Fin 2 → AF F) :=
  (eQ b).trans ((LinearEquiv.prodComm (AF F) _ _).trans (by
    first
    | exact (bM bs).equivFun.prodCongr ((bM bs).equivFun.trans
        (@Matrix.toLinearEquiv' _ _ _ _ _ (Pm σ J bs) (Matrix.invertibleOfIsUnitDet _ hP)))
    | exact (bM bs).equivFun.prod ((bM bs).equivFun.trans
        (@Matrix.toLinearEquiv' _ _ _ _ _ (Pm σ J bs) (Matrix.invertibleOfIsUnitDet _ hP)))))

theorem eD_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (b : GL (Fin n ⊕ Fin n) E)
    (hP : IsUnit (Pm (n := n) σ J bs).det) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    eD σ J bs b hP w = ((bM bs).equivFun (eQ b w).2, Pm σ J bs *ᵥ (bM bs).equivFun (eQ b w).1) := rfl

theorem eD_frame [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (b : GL (Fin n ⊕ Fin n) E) (hP : IsUnit (Pm (n := n) σ J bs).det) (Z X : Mx F E m n) :
    eD σ J bs b hP (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (crdB bs X, fun k => Bf σ J Z (Ek bs k)) := by
  rw [eD_apply, eQ_frame]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact bM_repr bs X k
  · show (Pm σ J bs *ᵥ (bM bs).equivFun Z) k = Bf σ J Z (Ek bs k)
    rw [Bf_eq_sum_left σ J bs Z (Ek bs k)]
    simp only [Matrix.mulVec, dotProduct, Module.Basis.equivFun_apply, bM_repr, Pm, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Bf_Ek_Ek, mul_comm]

theorem eD_form [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (YJ : Matrix (Fin n) (Fin n) E) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε)
    (u : ℤ) (hsym : ∀ X Z : Mx F E m n, Bf σ J X Z = (u : AF F) * Bf σ J Z X) (hεu : (ε : ℤ) * u = -1)
    (hP : IsUnit (Pm (n := n) σ J bs).det) (w w' : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (dbl (incM F YJ)) w w' =
      (eD σ J bs b hP w).1 ⬝ᵥ (eD σ J bs b hP w').2 - (eD σ J bs b hP w').1 ⬝ᵥ (eD σ J bs b hP w).2 := by
  obtain ⟨⟨Z, X⟩, rfl⟩ := (eQ (m := m) b).symm.surjective w
  obtain ⟨⟨Z', X'⟩, rfl⟩ := (eQ (m := m) b).symm.surjective w'
  rw [eQ_symm_apply, eQ_symm_apply, symp_frame σ J YJ b ε hb, eD_frame, eD_frame]
  simp only [dotProduct]
  rw [← Bf_eq_sum_right σ J bs Z' X, ← Bf_eq_sum_right σ J bs Z X', hsym X Z']
  have h1 : ((ε : ℤ) : AF F) * (u : AF F) = -1 := by rw [← Int.cast_mul, hεu]; norm_num
  linear_combination (-(Bf σ J Z' X)) * h1

theorem sDarb : SDarb := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε
  haveI : FiniteDimensional F E := Module.Finite.of_basis bs
  have hσ : ∀ a, σ (σ a) = a := by
    obtain ⟨-, -, -, h⟩ := hB.cm
    intro a
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    rw [h, h, star_star]
  obtain ⟨u, hsym, hεu, hJ⟩ : ∃ u : ℤ, (∀ i j, σ (A.J j i) = (u : E) * A.J i j) ∧ (ε : ℤ) * u = -1 ∧ A.J.det ≠ 0 := by
    rcases hsg with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, fun i j => by simp [hA.herm], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig B A.J hA.sig⟩
      rw [eps_eq hσ Y.J (-1) (fun i j => by simp [hY]) b ε hε hn]
      norm_num
    · refine ⟨-1, fun i j => by simp [hA.skew], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig' B A.J hA.sig⟩
      rw [eps_eq hσ Y.J 1 (fun i j => by simp [hY]) b ε hε hn]
      norm_num
  have hP := Pm_unit (n := n) σ hσ A.J hJ bs
  let dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2) :=
    ⟨eD σ A.J bs b hP, eD_form σ A.J bs Y.J b ε hε u (fun X Z => Bf_symm hσ A.J u hsym X Z) hεu hP⟩
  have hd : IsAdapted bs A Y b dd := fun Z X => eD_frame σ A.J bs b hP Z X
  refine ⟨dd, hd, fun x => ?_⟩
  obtain ⟨c, hc⟩ := e_rat bs A Y b dd hd x
  exact ⟨_, c, hc⟩

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
