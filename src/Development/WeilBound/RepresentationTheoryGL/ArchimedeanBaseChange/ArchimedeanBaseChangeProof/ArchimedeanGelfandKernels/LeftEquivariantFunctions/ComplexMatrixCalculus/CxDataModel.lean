import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.HasDerivAtConjTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrMulK
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.SwapLawsOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.GtCharZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.DerTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.RmAnti
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.DifferentiableMt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.SumKronLeft
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.FrameInvMulSymZero

section
noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem trace_clm (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    LinearMap.trace ℂ (EV n lam) ((clm lam A : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = A.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Ix n lam) ℂ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, clm, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem trace_cj (hu : IsUnit (sqQ lam)) (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    LinearMap.trace ℂ (EV n lam) ((cjL lam A : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = A.trace := by
  rw [cjL_apply, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, LinearMap.trace_mul_comm, ← mul_assoc,
    ← ContinuousLinearMap.coe_mul, ← ContinuousLinearMap.coe_mul, Ring.inverse_mul_cancel _ hu, one_mul, trace_clm]

theorem weylChar_conj (u : Fin n → ℂ) : weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀, map_pow]

theorem trace_gamma_zero_eq_one (hScal : GamScal) : (gamM (0 : Matrix (Md n) (Md n) ℂ)).trace = 1 := by
  have e : (0 : Matrix (Md n) (Md n) ℂ) = (0 : ℂ) • 1 := by rw [zero_smul]
  rw [e, hScal n 0, trace_diagonal, Finset.sum_eq_single (∅ : Finset (Md n))]
  · simp
  · intro A _ hA
    exact zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hA))
  · simp

theorem diag_unit_prod (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z)ᴴ * (diagonal z)⁻¹ = diagonal (fun a => conj (z a ^ 2)) ∧ IsUnit (diagonal z).det ∧
      IsUnit ((diagonal z)ᴴ).det ∧ IsUnit ((diagonal z)⁻¹).det := by
  have hc : ∀ a, z a * conj (z a) = 1 := fun a => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]; simp
  have hinv : (diagonal z)⁻¹ = diagonal fun a => conj (z a) :=
    Matrix.inv_eq_right_inv (by rw [diagonal_mul_diagonal]; simp [hc])
  have hne : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hinv, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1; ext a; simp [pow_two, map_mul]
  · rw [det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hne a)
  · rw [diagonal_conjTranspose, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using hne a)
  · rw [hinv, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using hne a)

theorem char_f (hu : IsUnit (sqQ lam)) (hG : GamMul) (hScal : GamScal) (hS : SwapLaws) (hRL : RmLaws) (hRC : RmChar)
    (hlam : Antitone lam) (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) (hinj : Function.Injective fun a => z a ^ 2) :
    LinearMap.trace ℂ (EV n lam) ((lefS n lam 0 * lefFr n lam (diagonal z) * lefT n lam : EV n lam →L[ℂ] EV n lam) :
      EV n lam →ₗ[ℂ] EV n lam) = conj (weylChar lam fun a => z a ^ 2) := by
  obtain ⟨hprod, hd, hdH, hdi⟩ := diag_unit_prod z hz
  rw [lefS_zero, lefFr_apply, lefT_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, zero_mul, mul_one, one_mul, trace_cj hu, trace_kronecker, trace_gamma_zero_eq_one hScal, one_mul,
    rhoW, (hS n lam).2.2.2.2, ← transpose_mul, trace_transpose]
  have hR := hRL n lam
  have hinvR : (Rm lam (diagonal z))⁻¹ = Rm lam (diagonal z)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hR.2.1 _ _ hd hdi, Matrix.mul_nonsing_inv _ hd, hR.1]
  rw [hinvR, ← hR.2.1 _ _ hdH hdi, hprod]
  have ht : ∀ a, (fun a => conj (z a ^ 2)) a ≠ 0 := fun a h => by
    have : z a ≠ 0 := fun h0 => by simpa [h0] using hz a
    simp only [map_eq_zero] at h
    exact this (pow_eq_zero_iff two_ne_zero |>.mp h)
  have hti : Function.Injective fun a => conj (z a ^ 2) := fun a b h => hinj (by
    have h' : conj (z a ^ 2) = conj (z b ^ 2) := h
    exact (RingHom.injective (starRingEnd ℂ)) h')
  rw [hRC n lam hlam _ ht hti, ← weylChar_conj]

end PositivityTheory.RgBcC
end
end

section
noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem kron_conjTranspose' {ι₁ ι₂ : Type*} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext i j; simp [kroneckerMap_apply, conjTranspose_apply, mul_comm]

theorem U_mem (hS : SwapLaws) :
    ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) ∈ Matrix.unitaryGroup (Ix n lam) ℂ := by
  have h := (hS n lam).2.1
  rw [Matrix.mem_unitaryGroup_iff] at h ⊢
  rw [Matrix.star_eq_conjTranspose, kron_conjTranspose', conjTranspose_one, ← mul_kronecker_mul, mul_one,
    ← Matrix.star_eq_conjTranspose, h, one_kronecker_one]

theorem Tiso_f (hu : IsUnit (sqQ lam)) (hA : Avg) (hS : SwapLaws) (v : EV n lam) : ‖lefT n lam v‖ = ‖v‖ := by
  set U := (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam
  have hU := U_mem (lam := lam) hS
  have hc : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U := by
    intro k
    rw [frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, swap_rhoW_k hu hS k]
  have hcomm := (hA n lam).2.2.2.2 U hU hc
  have e : lefT n lam = clm lam U := by
    rw [lefT_apply, cjL_apply, ← hcomm, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
  rw [e]
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  rw [Unitary.mem_iff]
  have hs : star (clm lam U) = clm lam (star U) := (map_star _ U).symm
  rw [hs, ← clm_mul', ← clm_mul', Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, clm_one']
  exact ⟨rfl, rfl⟩

theorem smooth_f (hF : MatrixFrechetDerivativeAtZeroLaws) : ContDiffOn ℝ ∞ (lefFr n lam) (GLs n) := by
  have h := ((cjL lam).restrictScalars ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn (hF n lam).2.2
  exact h

theorem one_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) : lefFr n lam 1 = 1 := by
  rw [lefFr_apply, (hF n lam).1, cj_one hu]

theorem mul_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) (x : Mat n) (hx : x ∈ GLs n) (y : Mat n) (hy : y ∈ GLs n) :
    lefFr n lam (x * y) = lefFr n lam x * lefFr n lam y := by
  rw [lefFr_apply, lefFr_apply, lefFr_apply, cj_mul hu,
    (hF n lam).2.1 x y (isUnit_iff_ne_zero.mpr hx) (isUnit_iff_ne_zero.mpr hy)]

theorem lefS_diag (hScal : GamScal) (s : ℝ) : lefS n lam s =
    cjL lam (krL n lam (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card)) := by
  rw [lefS_apply, hScal n]; rfl

theorem Ssmooth_f (hScal : GamScal) : ContDiff ℝ ∞ (lefS n lam) := by
  have e : lefS n lam = fun s : ℝ => (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
      (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  rw [e]
  refine ContinuousLinearMap.contDiff _ |>.comp ?_
  refine contDiff_pi.2 fun A => contDiff_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]; exact (Complex.ofRealCLM.contDiff).pow _
  · simp only [diagonal_apply_ne _ h]; exact contDiff_const

theorem hasDerivAt_diagPow (s : ℝ) : HasDerivAt (fun s : ℝ => (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card))
    (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1)) s := by
  refine hasDerivAt_pi.2 fun A => hasDerivAt_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]
    exact (hasDerivAt_pow A.card (s : ℂ)).comp_ofReal
  · simp only [diagonal_apply_ne _ h]; exact hasDerivAt_const _ _

theorem Sder_f (hu : IsUnit (sqQ lam)) (hScal : GamScal) (hN : Number) (s : ℝ) :
    deriv (lefS n lam) s = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
  set L := (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
  have e : lefS n lam = fun s : ℝ => L (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  have hd : HasDerivAt (lefS n lam) (L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))) s := by
    rw [e]; exact L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_diagPow s)
  rw [hd.deriv]
  have hcf : ∀ p : Fin n × Fin n, cf n (hb p) = Pi.single (finProdFinEquiv p) 1 := fun p => by
    have := Cxa.cf_hbM (n := n) (finProdFinEquiv p)
    simpa [hbM] using this
  have key : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
      annL n (cf n (hb p)) = Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1) := by
    rw [← hN n (s : ℂ)]
    exact Fintype.sum_equiv finProdFinEquiv _ _ (fun p => by rw [hcf p])
  calc L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))
      = cjL lam (krL n lam (∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [key]; rfl
    _ = ∑ p : Fin n × Fin n, cjL lam (krL n lam (creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [map_sum, map_sum]
    _ = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lefε_apply, lefι_apply, lefS_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul,
          mul_one, mul_one]
        rfl

end PositivityTheory.RgBcC
end
end

section
namespace PositivityTheory.RgBcC

theorem fr0Laws : MatrixFrechetDerivativeAtZeroLaws := fr0Laws_of rmLaws gamMul mtLaws gamDer

theorem avg : Avg := avg_of fr0Laws

theorem frOne : FrOne := frOne' fr0Laws avg
theorem frMulK : FrMulK := frMulK' fr0Laws avg
theorem frIso : FrIso := frIso' fr0Laws avg
theorem frCont : FrCont := frCont' fr0Laws avg

end PositivityTheory.RgBcC
end

section
noncomputable section

namespace PositivityTheory.RgBcC

def lefRho (n : ℕ) (lam : Fin n → ℤ) : Matrix.unitaryGroup (Fin n) ℂ →* (EV n lam →L[ℂ] EV n lam) where
  toFun k := lefFr n lam k.1
  map_one' := frOne n lam
  map_mul' k k' := frMulK n lam k k'

def lefE (n : ℕ) (lam : Fin n → ℤ) : KMod n where
  V := EV n lam
  ρ := lefRho n lam
  iso := frIso n lam
  cont := frCont n lam

end PositivityTheory.RgBcC
end
end

section
noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cxData_of (hCP : CfPair) (hM : MtLaws) (hG : GamMul) (hB : Car) (hC : GamCre) (hScal : GamScal) (hN : Number)
    (hRL : RmLaws) (hRC : RmChar) (hA : Avg) (hF : MatrixFrechetDerivativeAtZeroLaws) (hS : SwapLaws)
    (hTD : ∀ (n : ℕ) (lam : Fin n → ℤ), lefT n lam * (∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) =
      -((∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) * lefT n lam))
    (hEig : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ w : EV n lam,
      IsEig (infOf lam) fun x => lefFr n lam x⁻¹ (lefS n lam 0 w))
    {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hQ : IsUnit (sqQ lam) := (hA n lam).1
  exact
    { smooth := smooth_f hF
      one := one_f hQ hF
      mul := mul_f hQ hF
      onK := fun k => rfl
      car := car_f hQ hB hCP
      frι := frι_f hQ hC hM
      frε := frε_f hQ hC hM
      Γsq := Γsq_f hQ hG
      Γε := Γε_f hQ hG hC
      Γι := Γι_f hQ hG hC
      ΓFr := fun x _ => ΓFr_f hQ hG x
      ΓT := ΓT_f hQ hG
      Tsq := Tsq_f hQ hS
      Tiso := Tiso_f hQ hA hS
      TK := TK_f hQ hS
      Tε := Tε_f hQ hS
      Tι := Tι_f hQ hS
      TD := hTD n lam
      Ssmooth := Ssmooth_f hScal
      S1 := sym_one_eq_one hQ hG
      Sε := Sε_f hQ hG hC
      Sder := Sder_f hQ hScal hN
      SΓ := SΓ_f hQ hG
      S0sq := S0sq_f hQ hG
      S0Γ := S0Γ_f hQ hG
      sym_zero_comm_frame := fun x _ => sym_zero_comm_frame_matrix hQ hG x
      time_comm_sym_zero := time_comm_sym_zero_matrix hQ hG
      S0θ := S0θ_f hQ hS hG
      eig := hEig n lam hlam
      char := char_f hQ hG hScal hS hRL hRC hlam }

end PositivityTheory.RgBcC
end
end

section
namespace PositivityTheory.RgBcC

theorem cxData_model {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hsw : SwapLaws := swapLaws_of rmLaws
  have hfd : MatrixFrechetDerivativeAtZero := fr0Der_of gamDer gamMul mtLaws rmLaws
  exact cxData_of cfPair mtLaws gamMul car gamCre gamScal number rmLaws rmChar avg fr0Laws hsw
    (tdOf avg hbOrtho hsw hfd (wedgeDer_of gamDer))
    (eigOf avg gamMul rmLaws rmHol rmAnti eigProd eigLocal) lam hlam

theorem cxEx_model : CxEx := fun n lam hlam =>
  ⟨lefE n lam, lefFr n lam, lefε n lam, lefι n lam, lefS n lam, lefΓ n lam, lefT n lam, cxData_model lam hlam⟩

end PositivityTheory.RgBcC
end
