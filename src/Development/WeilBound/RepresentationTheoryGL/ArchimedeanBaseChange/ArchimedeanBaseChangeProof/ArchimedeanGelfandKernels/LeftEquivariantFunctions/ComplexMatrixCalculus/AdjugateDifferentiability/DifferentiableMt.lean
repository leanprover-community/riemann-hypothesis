import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigLocal

section
noncomputable section

open Matrix
open scoped Kronecker

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι]

theorem dEntry {F : E → Matrix κ μ ℂ} (h : DifferentiableAt ℝ F x) (i : κ) (j : μ) :
    DifferentiableAt ℝ (fun y => F y i j) x :=
  differentiableAt_pi.1 (differentiableAt_pi.1 h i) j

theorem dMat {F : E → Matrix κ μ ℂ} (h : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x) : DifferentiableAt ℝ F x :=
  differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j

theorem dMul {F : E → Matrix κ ι ℂ} {H : E → Matrix ι μ ℂ} (hF : DifferentiableAt ℝ F x) (hH : DifferentiableAt ℝ H x) :
    DifferentiableAt ℝ (fun y => F y * H y) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (dEntry hF i k).mul (dEntry hH k j)

theorem dConjT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᴴ) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (dEntry hF j i).star

theorem dT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᵀ) x := dMat fun i j => dEntry hF j i

theorem dConst (A : Matrix κ μ ℂ) : DifferentiableAt ℝ (fun _ : E => A) x := differentiableAt_const A

theorem differentiable_det : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.det) := by
  intro A0
  simp only [Matrix.det_apply, Units.smul_def]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_smul ?_ _
  exact (HasFDerivAt.finsetProd fun i _ =>
    (dEntry (differentiableAt_id (x := A0)) (σ i) i).hasFDerivAt).differentiableAt

theorem differentiable_adjugate : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.adjugate) := by
  intro A0
  refine dMat fun i j => ?_
  simp only [Matrix.adjugate_apply]
  have hu : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A.updateRow j (Pi.single i 1)) A0 := by
    refine dMat fun k l => ?_
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hk]
      exact dEntry differentiableAt_id k l
  exact (differentiable_det _).comp A0 hu

theorem differentiableAt_inv (A0 : Matrix ι ι ℂ) (h : A0.det ≠ 0) : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A⁻¹) A0 := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((differentiable_det A0).inv h).smul (differentiable_adjugate A0)

end PositivityTheory.RgBcC.Cxf
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (X : Mat n) :
    ∀ x ∈ U, Rd X f x = Rd X f' x := by
  intro x hx
  unfold Rd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (a b : Fin n) :
    ∀ x ∈ U, Eu s a b f x = Eu s a b f' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h (single a b 1) x hx, rd_congr hU h (single a b Complex.I) x hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), ∀ x ∈ U, Epow s m a b f x = Epow s m a b f' x := by
  intro m
  induction m with
  | zero =>
    intro a b x hx
    simp only [Epow.eq_1]
    by_cases hab : a = b <;> simp [hab, h x hx]
  | succ m ih =>
    intro a b x hx
    simp only [Epow.eq_2]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (fun y hy => ih c b y hy) s a c x hx

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (m : ℕ) :
    ∀ x ∈ U, gel s m f x = gel s m f' x := by
  intro x hx
  simp only [gel]
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU h s m a a x hx

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf in
theorem eigLocal : EigLocal := by
  intro n χ V _ _ f f' h hf s m g hg
  rw [← h g hg, ← gel_congr isOpen_GLs h s m g hg]
  exact hf s m g hg

end PositivityTheory.RgBcC
end
end

section
noncomputable section

open Matrix
open scoped Kronecker

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {κ μ : Type} [Fintype κ] [Fintype μ]

def kronLin (κ μ : Type) [Fintype κ] [Fintype μ] :
    Matrix κ κ ℂ →ₗ[ℝ] Matrix μ μ ℂ →ₗ[ℝ] Matrix (κ × μ) (κ × μ) ℂ :=
  LinearMap.mk₂ ℝ (fun A B => A ⊗ₖ B) (fun A A' B => Matrix.add_kronecker A A' B)
    (fun c A B => by rw [Matrix.smul_kronecker]) (fun A B B' => Matrix.kronecker_add A B B')
    (fun c A B => by rw [Matrix.kronecker_smul])

def kronC (κ μ : Type) [Fintype κ] [Fintype μ] :
    Matrix κ κ ℂ →L[ℝ] Matrix μ μ ℂ →L[ℝ] Matrix (κ × μ) (κ × μ) ℂ :=
  LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (Matrix μ μ ℂ →ₗ[ℝ] Matrix (κ × μ) (κ × μ) ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ kronLin κ μ)

variable {n : ℕ}

theorem differentiable_Mt : Differentiable ℝ (Mt (n := n)) := by
  intro y
  refine dMat fun p q => ?_
  have hM : DifferentiableAt ℝ (fun z : Mat n => z * hbM q * zᴴ * hbM p) y :=
    dMul (dMul (dMul differentiableAt_id (dConst _)) (dConjT differentiableAt_id)) (dConst _)
  have ht : DifferentiableAt ℝ (fun z : Mat n => (z * hbM q * zᴴ * hbM p).trace) y := by
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun i _ => dEntry hM i i
  exact (Complex.ofRealCLM.comp Complex.reCLM).differentiableAt.comp y ht

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fr0Der_of (hG : GamDer) (hGm : GamMul) (hM : MtLaws) (hR : RmLaws) : MatrixFrechetDerivativeAtZero := by
  intro n lam
  have hdet1 : (1 : PositivityTheory.RgTw.Mat n).det ≠ 0 := by simp
  have hopen : IsOpen (GLs n) :=
    isOpen_ne_fun (differentiable_det (ι := Fin n)).continuous continuous_const
  have hRm : ∀ y : PositivityTheory.RgTw.Mat n, y.det ≠ 0 → DifferentiableAt ℝ (Rm lam) y := fun y hy =>
    ((hR n lam).2.2.contDiffAt (hopen.mem_nhds (show y ∈ GLs n from hy))).differentiableAt (by simp)
  have hdetR : (Rm lam (1 : PositivityTheory.RgTw.Mat n)).det ≠ 0 := by rw [(hR n lam).1]; simp
  have hgam : ∀ B : Matrix (Md n) (Md n) ℂ, DifferentiableAt ℝ (gamM (n := n)) B := fun B =>
    (((hG n).1.differentiable (by simp)) B).restrictScalars ℝ
  have hFd : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => gamM (Mt x⁻¹)ᵀ) 1 :=
    (hgam _).comp (1 : PositivityTheory.RgTw.Mat n)
      (dT ((differentiable_Mt _).comp (1 : PositivityTheory.RgTw.Mat n) (differentiableAt_inv 1 hdet1)))
  have hA : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => (Rm lam x)⁻¹ᵀ) 1 :=
    dT ((differentiableAt_inv _ hdetR).comp (1 : PositivityTheory.RgTw.Mat n) (hRm 1 hdet1))
  have hB : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => (Rm lam xᴴ)ᵀ) 1 :=
    dT ((hRm _ (by simp)).comp (1 : PositivityTheory.RgTw.Mat n) (dConjT differentiableAt_id))
  have hGd : DifferentiableAt ℝ (rhoW lam) 1 := by
    have h := ((kronC _ _).hasFDerivAt_of_bilinear hA.hasFDerivAt hB.hasFDerivAt).differentiableAt
    exact h
  have key : fr0 lam = fun x => kronC _ _ (gamM (Mt x⁻¹)ᵀ) (rhoW lam x) := rfl
  have hF1 : gamM (Mt (1 : PositivityTheory.RgTw.Mat n)⁻¹)ᵀ = 1 := by
    rw [inv_one, (hM n).1, transpose_one, (hGm n).1]
  have hG1 : rhoW lam (1 : PositivityTheory.RgTw.Mat n) = 1 := by
    simp only [rhoW, conjTranspose_one, (hR n lam).1, inv_one, transpose_one]
    exact Matrix.one_kronecker_one
  refine ⟨?_, fun X _ => ?_⟩
  · rw [key]
    exact ((kronC _ _).hasFDerivAt_of_bilinear hFd.hasFDerivAt hGd.hasFDerivAt).differentiableAt
  · have h := congrArg (fun L => L X) ((kronC _ _).fderiv_of_bilinear hFd hGd)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, hF1, hG1] at h
    rw [key]
    refine h.trans ?_
    rw [add_comm]
    rfl

end PositivityTheory.RgBcC
end
end
