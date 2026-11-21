import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.SwmConeStatements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.InstSecondCountableTopologyFrameSp
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.FramePairAddRight
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.ContinuousFramePairLeft
import GroundTheory.HeightsAndTheta.Theta.SchroedingerTranslates.WmSysEquivDet

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace SwmCone

open MeasureTheory Topology Filter Matrix TensorProduct GroundTheory.Automorphic IsoFrames
open scoped ENNReal NNReal

attribute [local instance] IsoFrames.scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

section Linear

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

instance instModuleFrameSpSwmCone : Module R (FrameSp K E R ι n) :=
  inferInstanceAs (Module R (ι → Fin n → R ⊗[K] E))

instance instIsModuleTopologyFrameSpSwmCone : IsModuleTopology R (FrameSp K E R ι n) :=
  inferInstanceAs (IsModuleTopology R (ι → Fin n → R ⊗[K] E))

instance instFiniteDimensionalFrameSpSwmCone : FiniteDimensional R (FrameSp K E R ι n) :=
  inferInstanceAs (Module.Finite R (ι → Fin n → R ⊗[K] E))

variable (K E R ι n) in

def frameMulLinA (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    (ι → Fin n → R ⊗[K] E) →ₗ[R ⊗[K] E] (ι → Fin n → R ⊗[K] E) :=
  LinearMap.pi fun i ↦ (Matrix.toLin' gᵀ).comp (LinearMap.proj i)

theorem frameMulLinA_apply (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (X : ι → Fin n → R ⊗[K] E) :
    frameMulLinA K E R ι n g X = (Matrix.of X * g : Matrix ι (Fin n) (R ⊗[K] E)) := by
  ext i j
  simp only [frameMulLinA, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.toLin'_apply]
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rfl


variable (K E R ι n) in

def frameMulLin (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    FrameSp K E R ι n →ₗ[R] FrameSp K E R ι n :=
  (frameMulLinA K E R ι n g).restrictScalars R

theorem frameMulLin_apply (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameMulLin K E R ι n g X = frameMul X g :=
  frameMulLinA_apply g X


end Linear

section Modulus

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]

theorem absF_mul (a b : F) :
    IndefiniteRowSideFullHecke.WmSys.absF (a * b) = IndefiniteRowSideFullHecke.WmSys.absF a * IndefiniteRowSideFullHecke.WmSys.absF b := by
  by_cases ha : a = 0
  · simp [IndefiniteRowSideFullHecke.WmSys.absF, ha]
  by_cases hb : b = 0
  · simp [IndefiniteRowSideFullHecke.WmSys.absF, hb]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [IndefiniteRowSideFullHecke.WmSys.absF, dif_neg ha, dif_neg hb, dif_neg hab]
  rw [show Units.mk0 (a * b) hab = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]



variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable [Algebra K F]





end Modulus

section FrameMul

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem frameMul_frameMul (X : FrameSp K E R ι n) (g h : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    frameMul (frameMul X g) h = frameMul X (g * h) :=
  Matrix.mul_assoc (X : Matrix ι (Fin n) (R ⊗[K] E)) g h

theorem frameMul_one (X : FrameSp K E R ι n) : frameMul X 1 = X :=
  Matrix.mul_one (X : Matrix ι (Fin n) (R ⊗[K] E))

variable (K E R ι n) in

def frameMulLinEquiv (g : GL (Fin n) (R ⊗[K] E)) : FrameSp K E R ι n ≃ₗ[R] FrameSp K E R ι n :=
  { frameMulLin K E R ι n (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) with
    invFun := frameMulLin K E R ι n ((g⁻¹ : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))
    left_inv := fun X ↦ by
      show frameMulLin K E R ι n _ (frameMulLin K E R ι n _ X) = X
      rw [frameMulLin_apply, frameMulLin_apply, frameMul_frameMul, Units.mul_inv, frameMul_one]
    right_inv := fun X ↦ by
      show frameMulLin K E R ι n _ (frameMulLin K E R ι n _ X) = X
      rw [frameMulLin_apply, frameMulLin_apply, frameMul_frameMul, Units.inv_mul, frameMul_one] }

variable (K E R ι n) in

def frameMulHom (g : GL (Fin n) (R ⊗[K] E)) : FrameSp K E R ι n ≃ₜ+ FrameSp K E R ι n :=
  { (frameMulLinEquiv K E R ι n g).toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (frameMulLinEquiv K E R ι n g).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (frameMulLinEquiv K E R ι n g).symm.toLinearMap }

@[simp]
theorem frameMulHom_apply (g : GL (Fin n) (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameMulHom K E R ι n g X = frameMul X (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :=
  frameMulLin_apply _ X

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]


end FrameMul

section FrameSMul

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def transposePi (S : Type*) [CommRing S] (m κ : Type*) :
    (m → κ → S) ≃ₗ[S] (κ → m → S) where
  toFun X j i := X i j
  invFun Y i j := Y j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def rowMulLinA {S : Type*} [CommRing S] (m : Type*) {κ : Type*} [Fintype m] [Fintype κ]
    [DecidableEq κ] (g : Matrix κ κ S) : (m → κ → S) →ₗ[S] (m → κ → S) :=
  LinearMap.pi fun i ↦ (Matrix.toLin' gᵀ).comp (LinearMap.proj i)

theorem rowMulLinA_apply {S : Type*} [CommRing S] {m κ : Type*} [Fintype m] [Fintype κ]
    [DecidableEq κ] (g : Matrix κ κ S) (X : m → κ → S) :
    rowMulLinA m g X = (Matrix.of X * g : Matrix m κ S) := by
  ext i j
  simp only [rowMulLinA, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.toLin'_apply]
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]
  rfl


def colMulLinA {S : Type*} [CommRing S] {m : Type*} (κ : Type*) [Fintype m] [DecidableEq m]
    [Fintype κ] (h : Matrix m m S) : (m → κ → S) →ₗ[S] (m → κ → S) :=
  ((transposePi S m κ).symm.toLinearMap.comp (rowMulLinA κ hᵀ)).comp
    (transposePi S m κ).toLinearMap

theorem colMulLinA_apply {S : Type*} [CommRing S] {m κ : Type*} [Fintype m] [DecidableEq m]
    [Fintype κ] (h : Matrix m m S) (X : m → κ → S) :
    colMulLinA κ h X = (h * Matrix.of X : Matrix m κ S) := by
  ext i j
  simp only [colMulLinA, LinearMap.comp_apply, LinearEquiv.coe_coe, rowMulLinA_apply]
  show (Matrix.of (fun j i ↦ X i j) * hᵀ) j i = (h * Matrix.of X) i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _


variable (K E R ι n) in

def frameSMulLin (h : Matrix ι ι (R ⊗[K] E)) : FrameSp K E R ι n →ₗ[R] FrameSp K E R ι n :=
  (colMulLinA (Fin n) h).restrictScalars R

theorem frameSMulLin_apply (h : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameSMulLin K E R ι n h X = frameSMul h X :=
  colMulLinA_apply h X


theorem frameSMul_frameSMul (h h' : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameSMul h (frameSMul h' X) = frameSMul (h * h') X :=
  (Matrix.mul_assoc h h' (X : Matrix ι (Fin n) (R ⊗[K] E))).symm

theorem frameSMul_one (X : FrameSp K E R ι n) : frameSMul (1 : Matrix ι ι (R ⊗[K] E)) X = X :=
  Matrix.one_mul (X : Matrix ι (Fin n) (R ⊗[K] E))

variable (K E R ι n) in

def frameSMulLinEquiv (h : GL ι (R ⊗[K] E)) : FrameSp K E R ι n ≃ₗ[R] FrameSp K E R ι n :=
  { frameSMulLin K E R ι n (h : Matrix ι ι (R ⊗[K] E)) with
    invFun := frameSMulLin K E R ι n ((h⁻¹ : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))
    left_inv := fun X ↦ by
      show frameSMulLin K E R ι n _ (frameSMulLin K E R ι n _ X) = X
      rw [frameSMulLin_apply, frameSMulLin_apply, frameSMul_frameSMul, Units.inv_mul, frameSMul_one]
    right_inv := fun X ↦ by
      show frameSMulLin K E R ι n _ (frameSMulLin K E R ι n _ X) = X
      rw [frameSMulLin_apply, frameSMulLin_apply, frameSMul_frameSMul, Units.mul_inv, frameSMul_one] }

variable (K E R ι n) in

def frameSMulHom (h : GL ι (R ⊗[K] E)) : FrameSp K E R ι n ≃ₜ+ FrameSp K E R ι n :=
  { (frameSMulLinEquiv K E R ι n h).toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (frameSMulLinEquiv K E R ι n h).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (frameSMulLinEquiv K E R ι n h).symm.toLinearMap }

@[simp]
theorem frameSMulHom_apply (h : GL ι (R ⊗[K] E)) (X : FrameSp K E R ι n) :
    frameSMulHom K E R ι n h X = frameSMul (h : Matrix ι ι (R ⊗[K] E)) X :=
  frameSMulLin_apply _ X

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]


end FrameSMul

section Unitary

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

variable (K E R) in

def conjBaseAlgEquiv : (R ⊗[K] E) ≃ₐ[R] (R ⊗[K] E) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (conj K E)




variable [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]



end Unitary

section Gram

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem gram_mul_right (Q : Matrix ι ι E) (X : Matrix ι (Fin n) (R ⊗[K] E))
    (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    IsoFrames.gram K E R Q (X * g) = cTr K E R g * IsoFrames.gram K E R Q X * g := by
  rw [IsoFrames.gram, IsoFrames.gram, Chart.framePair_mul_left, Chart.framePair_mul_right,
    Matrix.mul_assoc]
  rfl




end Gram

section UnitaryHaar

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}


end UnitaryHaar

section Congr

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {n : ℕ}

theorem cTr_mul {l m k : Type*} [Fintype m] (M : Matrix l m (R ⊗[K] E)) (N : Matrix m k (R ⊗[K] E)) :
    cTr K E R (M * N) = cTr K E R N * cTr K E R M :=
  Chart.cT_mul M N

theorem cTr_cTr {l m : Type*} (M : Matrix l m (R ⊗[K] E)) : cTr K E R (cTr K E R M) = M :=
  Chart.cT_cT M

theorem cTr_one {m : Type*} [DecidableEq m] : cTr K E R (1 : Matrix m m (R ⊗[K] E)) = 1 :=
  Chart.cT_one

theorem HermSp.cTr_mat (S : HermSp K E R n) : cTr K E R S.mat = S.mat := S.2

theorem HermSp.ext' {S S' : HermSp K E R n} (h : S.mat = S'.mat) : S = S' := Subtype.ext h

theorem congr_mem (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    cTr K E R g * S.mat * g ∈ hermSub K E R n := by
  show cTr K E R (cTr K E R g * S.mat * g) = cTr K E R g * S.mat * g
  rw [cTr_mul, cTr_mul, cTr_cTr, HermSp.cTr_mat, Matrix.mul_assoc]

def congrPt (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) : HermSp K E R n :=
  ⟨cTr K E R g * S.mat * g, congr_mem g S⟩

@[simp]
theorem congrPt_mat (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    (congrPt g S).mat = cTr K E R g * S.mat * g := rfl

theorem congrPt_congrPt (g h : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    congrPt g (congrPt h S) = congrPt (h * g) S := by
  refine HermSp.ext' ?_
  simp only [congrPt_mat, cTr_mul, Matrix.mul_assoc]

theorem congrPt_one (S : HermSp K E R n) : congrPt 1 S = S := by
  refine HermSp.ext' ?_
  simp only [congrPt_mat, cTr_one, Matrix.one_mul, Matrix.mul_one]

theorem congrPt_add (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) (S S' : HermSp K E R n) :
    congrPt g (S + S') = congrPt g S + congrPt g S' := by
  refine HermSp.ext' ?_
  show cTr K E R g * (S.mat + S'.mat) * g = cTr K E R g * S.mat * g + cTr K E R g * S'.mat * g
  rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_congrPt (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    Continuous (congrPt (K := K) (E := E) (R := R) g) :=
  have hc : Continuous (fun S : HermSp K E R n ↦ S.mat) := continuous_induced_dom
  continuous_induced_rng.2 ((continuous_const.matrix_mul hc).matrix_mul continuous_const)

variable (K E R n) in

def congrHom (g : GL (Fin n) (R ⊗[K] E)) : HermSp K E R n ≃ₜ+ HermSp K E R n where
  toFun := congrPt (g : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  invFun := congrPt ((g⁻¹ : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  left_inv S := by rw [congrPt_congrPt, Units.mul_inv, congrPt_one]
  right_inv S := by rw [congrPt_congrPt, Units.inv_mul, congrPt_one]
  map_add' := congrPt_add _
  continuous_toFun := continuous_congrPt _
  continuous_invFun := continuous_congrPt _

@[simp]
theorem congrHom_mat (g : GL (Fin n) (R ⊗[K] E)) (S : HermSp K E R n) :
    (congrHom K E R n g S).mat = cTr K E R (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) * S.mat *
      (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) := rfl

variable (K E R n) in

def ctGL (g : GL (Fin n) (R ⊗[K] E)) : GL (Fin n) (R ⊗[K] E) where
  val := cTr K E R (g : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  inv := cTr K E R ((g⁻¹ : GL (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  val_inv := by rw [← cTr_mul, Units.inv_mul, cTr_one]
  inv_val := by rw [← cTr_mul, Units.mul_inv, cTr_one]

def congrAll (g : GL (Fin n) (R ⊗[K] E)) :
    FrameSp K E R (Fin n) n ≃ₜ+ FrameSp K E R (Fin n) n :=
  (frameSMulHom K E R (Fin n) n (ctGL K E R n g)).trans (frameMulHom K E R (Fin n) n g)


variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]


end Congr

section Split

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {n : ℕ}

theorem exists_conj_eq_neg_swm : ∃ δ : E, δ ≠ 0 ∧ conj K E δ = -δ := by
  have hx : ∃ x : E, x ∉ Set.range (algebraMap K E) := by
    by_contra h
    push Not at h
    have hbij : Function.Bijective (Algebra.linearMap K E) :=
      ⟨(algebraMap K E).injective, fun y ↦ h y⟩
    have h1 := (LinearEquiv.ofBijective (Algebra.linearMap K E) hbij).finrank_eq
    rw [Module.finrank_self, Algebra.IsQuadraticExtension.finrank_eq_two] at h1
    norm_num at h1
  obtain ⟨x, hx⟩ := hx
  refine ⟨x - conj K E x, ?_, ?_⟩
  · intro h0
    apply hx
    refine ⟨(2 : K)⁻¹ * Algebra.trace K E x, ?_⟩
    have h1 := add_conj (F := K) x
    have h2 : conj K E x = x := (sub_eq_zero.1 h0).symm
    rw [h2] at h1
    rw [map_mul, ← h1, ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap K E) 2, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero' K), map_one, one_mul]
  · rw [map_sub, conj_conj]
    ring

variable (K E R) in

def epsU : (R ⊗[K] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E).toMonoidHom
    (Units.mk0 (exists_conj_eq_neg_swm (K := K) (E := E)).choose
      (exists_conj_eq_neg_swm (K := K) (E := E)).choose_spec.1)

theorem conjBase_epsU : conjBase K E R (epsU K E R : R ⊗[K] E) = -(epsU K E R : R ⊗[K] E) := by
  show conjBase K E R ((1 : R) ⊗ₜ[K] (exists_conj_eq_neg_swm (K := K) (E := E)).choose) =
    -((1 : R) ⊗ₜ[K] (exists_conj_eq_neg_swm (K := K) (E := E)).choose)
  rw [conjBase_tmul, (exists_conj_eq_neg_swm (K := K) (E := E)).choose_spec.2, TensorProduct.tmul_neg]

theorem conjBase_epsU_inv :
    conjBase K E R ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ) = -((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ) := by
  have h1 := congrArg (conjBase K E R) (Units.inv_mul (epsU K E R))
  rw [map_mul, conjBase_epsU, map_one] at h1
  have h2 := Units.mul_inv (epsU K E R)
  linear_combination (-(conjBase K E R ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ))) * h2 -
    ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ) * h1

abbrev halfA (K E R : Type*) [Field K] [Field E] [Algebra K E] [CommRing R] [Algebra K R] :
    R ⊗[K] E := algebraMap K (R ⊗[K] E) (2 : K)⁻¹

theorem two_mul_halfA : (2 : R ⊗[K] E) * halfA K E R = 1 := by
  rw [halfA, ← map_ofNat (algebraMap K (R ⊗[K] E)) 2, ← map_mul,
    mul_inv_cancel₀ (two_ne_zero' K), map_one]

theorem conjBase_halfA : conjBase K E R (halfA K E R) = halfA K E R := by
  rw [halfA, Algebra.algebraMap_eq_smul_one, Chart.conjBase_smul, map_one]

theorem cTr_apply {l m : Type*} (M : Matrix l m (R ⊗[K] E)) (i : m) (j : l) :
    cTr K E R M i j = conjBase K E R (M j i) := rfl

theorem HermSp.mat_apply_swap (S : HermSp K E R n) (i j : Fin n) :
    conjBase K E R (S.mat j i) = S.mat i j := by
  have := congrFun (congrFun (HermSp.cTr_mat S) i) j
  rwa [cTr_apply] at this

def hPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E) :=
  halfA K E R • (X + cTr K E R X)

def sPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : Matrix (Fin n) (Fin n) (R ⊗[K] E) :=
  (halfA K E R * ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ)) • (X - cTr K E R X)

theorem hPartM_mem (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : hPartM X ∈ hermSub K E R n := by
  show cTr K E R (hPartM X) = hPartM X
  ext i j
  simp only [hPartM, cTr_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_mul, map_add,
    conjBase_halfA, Chart.conjBase_conjBase]
  ring

theorem sPartM_mem (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)) : sPartM X ∈ hermSub K E R n := by
  show cTr K E R (sPartM X) = sPartM X
  ext i j
  simp only [sPartM, cTr_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub,
    conjBase_halfA, conjBase_epsU_inv, Chart.conjBase_conjBase]
  ring

variable (K E R n) in

def splitHom : (HermSp K E R n × HermSp K E R n) ≃ₜ+ FrameSp K E R (Fin n) n where
  toFun p := (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat : Matrix (Fin n) (Fin n) (R ⊗[K] E))
  invFun X := (⟨hPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)), hPartM_mem _⟩,
    ⟨sPartM (X : Matrix (Fin n) (Fin n) (R ⊗[K] E)), sPartM_mem _⟩)
  left_inv p := by
    refine Prod.ext (HermSp.ext' ?_) (HermSp.ext' ?_)
    · ext i j
      show hPartM (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat) i j = p.1.mat i j
      simp only [hPartM, cTr_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, map_add,
        map_mul, conjBase_epsU, HermSp.mat_apply_swap]
      linear_combination (p.1.mat i j) * (two_mul_halfA (K := K) (E := E) (R := R))
    · ext i j
      show sPartM (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat) i j = p.2.mat i j
      simp only [sPartM, cTr_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
        smul_eq_mul, map_add, map_mul, conjBase_epsU, HermSp.mat_apply_swap]
      linear_combination (p.2.mat i j) * (two_mul_halfA (K := K) (E := E) (R := R)) +
        (2 * halfA K E R * p.2.mat i j) * Units.inv_mul (epsU K E R)
  right_inv X := by
    refine Matrix.ext fun i j ↦ ?_
    show (hPartM (Chart.toM X) + (epsU K E R : R ⊗[K] E) • sPartM (Chart.toM X)) i j =
      Chart.toM X i j
    simp only [hPartM, sPartM, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (Chart.toM X i j) * (two_mul_halfA (K := K) (E := E) (R := R)) +
      (halfA K E R * (Chart.toM X i j - cTr K E R (Chart.toM X) i j)) *
        Units.mul_inv (epsU K E R)
  map_add' p q := by
    show ((p.1 + q.1).mat + (epsU K E R : R ⊗[K] E) • (p.2 + q.2).mat : Matrix (Fin n) (Fin n) _) =
      (p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat) + (q.1.mat + (epsU K E R : R ⊗[K] E) • q.2.mat)
    rw [show (p.1 + q.1).mat = p.1.mat + q.1.mat from rfl,
      show (p.2 + q.2).mat = p.2.mat + q.2.mat from rfl, smul_add]
    abel
  continuous_toFun := by
    have hc : Continuous (fun S : HermSp K E R n ↦ S.mat) := continuous_induced_dom
    exact (hc.comp continuous_fst).add ((continuous_const_smul (epsU K E R : R ⊗[K] E)).comp
      (hc.comp continuous_snd))
  continuous_invFun := by
    have hct : Continuous (fun X : FrameSp K E R (Fin n) n ↦ cTr K E R (Chart.toM X)) :=
      (continuous_id.matrix_map (continuous_conjBase R)).matrix_transpose
    refine Continuous.prodMk ?_ ?_
    · refine continuous_induced_rng.2 ?_
      show Continuous fun X : FrameSp K E R (Fin n) n ↦
        halfA K E R • (Chart.toM X + cTr K E R (Chart.toM X))
      exact (continuous_const_smul _).comp
        ((show Continuous (fun X : FrameSp K E R (Fin n) n ↦ Chart.toM X) from continuous_id).add hct)
    · refine continuous_induced_rng.2 ?_
      show Continuous fun X : FrameSp K E R (Fin n) n ↦
        (halfA K E R * ((epsU K E R)⁻¹ : (R ⊗[K] E)ˣ)) •
          (Chart.toM X - cTr K E R (Chart.toM X))
      exact (continuous_const_smul _).comp
        ((show Continuous (fun X : FrameSp K E R (Fin n) n ↦ Chart.toM X) from continuous_id).sub hct)

theorem splitHom_apply (p : HermSp K E R n × HermSp K E R n) :
    Chart.toM (splitHom K E R n p) = p.1.mat + (epsU K E R : R ⊗[K] E) • p.2.mat := rfl


variable (K E R n) in

def congrPair (g : GL (Fin n) (R ⊗[K] E)) :
    (HermSp K E R n × HermSp K E R n) ≃ₜ+ (HermSp K E R n × HermSp K E R n) where
  toFun p := (congrHom K E R n g p.1, congrHom K E R n g p.2)
  invFun p := ((congrHom K E R n g).symm p.1, (congrHom K E R n g).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [map_add]
  continuous_toFun := (congrHom K E R n g).continuous.prodMap (congrHom K E R n g).continuous
  continuous_invFun :=
    (congrHom K E R n g).symm.continuous.prodMap (congrHom K E R n g).symm.continuous

variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]

open Measure in
theorem addEquivAddHaarChar_congrPair (g : GL (Fin n) (R ⊗[K] E)) :
    addEquivAddHaarChar (congrPair K E R n g) = addEquivAddHaarChar (congrHom K E R n g) ^ 2 := by
  set φ := congrHom K E R n g
  let μ : Measure (HermSp K E R n) := addHaar
  let P : Measure (HermSp K E R n × HermSp K E R n) := μ.prod μ
  obtain ⟨U, hUc, hU0⟩ : ∃ U : Set (HermSp K E R n), IsCompact U ∧ U ∈ 𝓝 (0 : HermSp K E R n) :=
    exists_compact_mem_nhds 0
  have hφU0 : φ ⁻¹' U ∈ 𝓝 (0 : HermSp K E R n) := by
    have hc : Tendsto (fun x ↦ φ x) (𝓝 0) (𝓝 (φ 0)) := φ.continuous.tendsto 0
    rw [map_zero] at hc
    exact hc hU0
  have hφUc : IsCompact (φ ⁻¹' U) := φ.toHomeomorph.isCompact_preimage.2 hUc
  have hpre : ⇑(congrPair K E R n g) ⁻¹' (U ×ˢ U) = (φ ⁻¹' U) ×ˢ (φ ⁻¹' U) := by
    ext p; rfl
  have hpos : μ (φ ⁻¹' U) ≠ 0 := (measure_pos_of_mem_nhds μ hφU0).ne'
  have hfin : μ (φ ⁻¹' U) ≠ ∞ := hφUc.measure_lt_top.ne
  have hs := addEquivAddHaarChar_smul_preimage μ (X := U) φ
  rw [ENNReal.smul_def, smul_eq_mul] at hs
  refine WmSysEquiv.addEquivAddHaarChar_eq_of_preimage P _ (S := U ×ˢ U) ?_ ?_ ?_
  · rw [hpre, Measure.prod_prod]
    exact mul_ne_zero hpos hpos
  · rw [hpre, Measure.prod_prod]
    exact ENNReal.mul_ne_top hfin hfin
  · rw [hpre, Measure.prod_prod, Measure.prod_prod, ← hs, ENNReal.coe_pow]
    ring


end Split

section Joint

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [Field R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}




variable [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]



end Joint

section Places

open NumberField IsDedekindDomain


variable {K : Type*} [Field K] [NumberField K]


theorem not_discreteTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    ¬ DiscreteTopology (v.adicCompletion K) := by
  intro hd
  have hfin := (GroundTheory.Global.isCompact_adicCompletionIntegers v).finite_of_discrete
  have hinj : Function.Injective (fun k : ℕ ↦ (k : v.adicCompletion K)) := by
    intro a b hab
    have : algebraMap K (v.adicCompletion K) (a : K) = algebraMap K (v.adicCompletion K) (b : K) := by
      simpa [map_natCast] using hab
    exact_mod_cast (algebraMap K (v.adicCompletion K)).injective this
  exact Set.infinite_of_injective_forall_mem hinj
    (fun k ↦ natCast_mem (v.adicCompletionIntegers K) k) hfin


theorem secondCountableTopology_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (v.adicCompletion K) :=
  locField_secondCountable (not_discreteTopology_adicCompletion v)

end Places

end SwmCone

end GroundTheory.Heights₂.Theta
