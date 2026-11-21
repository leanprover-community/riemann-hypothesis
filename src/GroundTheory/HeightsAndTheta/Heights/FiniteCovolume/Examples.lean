import Mathlib
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section General

variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]

theorem lineIndex_smul {h : HermitianForm F E W} {La : AddSubgroup W} {γ : h.unitaryGroup}
    (hγ : γ • La = La) (x : W) : lineIndex E La (γ • x) = lineIndex E La x := by
  let f : W →+ W := ((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom
  have hf : Function.Injective f := (γ : W ≃ₗ[E] W).injective
  have hfx : ∀ y : W, f y = γ • y := fun y => rfl
  have h1 : (ringMultiples E x).map f = ringMultiples E (γ • x) := by
    rw [ringMultiples, ringMultiples, ← AddMonoidHom.range_comp]
    congr 1
    ext a
    simp only [AddMonoidHom.comp_apply, hfx]
    simp [Subgroup.smul_def, LinearEquiv.smul_def]
  have h2 : La.map f = La := by
    conv_rhs => rw [← hγ]
    change La.map f = (γ : W ≃ₗ[E] W) • La
    rw [AddSubgroup.pointwise_smul_def]
    rfl
  have h3 : ((Submodule.span E {x}).toAddSubgroup).map f =
      (Submodule.span E {γ • x}).toAddSubgroup := by
    ext y
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [hfx, smul_comm]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c • x, ⟨c, rfl⟩, by rw [hfx, smul_comm]⟩
  unfold lineIndex
  conv_rhs => rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  rw [AddSubgroup.map_inf_eq _ _ f hf, h1, h2, h3]

end General

abbrev Eg : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ Eg := CyclotomicField.isCyclotomicExtension 4 ℚ

theorem finrank_Eg : finrank ℚ Eg = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Eg
    (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

instance : Algebra.IsQuadraticExtension ℚ Eg := { finrank_eq_two' := finrank_Eg }

instance : IsTotallyComplex Eg := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) Eg (by norm_num)

theorem card_infinitePlace : Fintype.card (InfinitePlace Eg) = 1 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank Eg
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, finrank_Eg] at h1
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  omega

instance : Subsingleton (InfinitePlace Eg) :=
  Fintype.card_le_one_iff_subsingleton.mp card_infinitePlace.le


def signs : Fin 2 → ℚˣ := ![1, -1]

def hG : HermitianForm ℚ Eg (Fin 2 → Eg) := diagForm signs

def vG : Basis (Fin 2) Eg (Fin 2 → Eg) := Pi.basisFun Eg (Fin 2)

theorem hG_apply (x y : Fin 2 → Eg) : hG.toSesq x y = conj ℚ Eg (x 0) * y 0 - conj ℚ Eg (x 1) * y 1 := by
  simp only [hG, diagForm, signs, LinearMap.mk₂'ₛₗ_apply, Fin.sum_univ_two]
  simp
  ring

theorem gram_hG : gram hG.toSesq vG = Matrix.diagonal ![1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Automorphic.gram_apply, vG, Pi.basisFun_apply] <;> rw [hG_apply] <;> simp

theorem gramAt_hG (w : InfinitePlace Eg) : gramAt hG vG w = Matrix.diagonal ![1, -1] := by
  rw [gramAt, gram_hG]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

def MG : Majorant hG vG where
  P _ := 1
  posDef _ := Matrix.PosDef.one
  siegel w := by
    rw [gramAt_hG, Matrix.one_mul, Matrix.mul_one]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

def LaG : AddSubgroup (Fin 2 → Eg) :=
  (AddMonoidHom.compLeft (algebraMap (𝓞 Eg) Eg).toAddMonoidHom (Fin 2)).range

theorem mem_LaG {x : Fin 2 → Eg} : x ∈ LaG ↔ ∀ i, x i ∈ integralClosure ℤ Eg := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (mem_integralClosure_iff ℤ Eg).2 (RingOfIntegers.isIntegral_coe (y i))
  · intro hx
    exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩

theorem conj_mem {z : Eg} (hz : z ∈ integralClosure ℤ Eg) : conj ℚ Eg z ∈ integralClosure ℤ Eg := by
  rw [mem_integralClosure_iff ℤ Eg] at *
  exact hz.map ((conj ℚ Eg).toAlgHom.restrictScalars ℤ)

theorem single_mem_LaG (i : Fin 2) : (Pi.single i 1 : Fin 2 → Eg) ∈ LaG := by
  rw [mem_LaG]
  intro j
  by_cases hij : j = i
  · subst hij
    simp only [Pi.single_eq_same]
    exact one_mem _
  · rw [Pi.single_eq_of_ne hij]
    exact zero_mem _




def v0 : Fin 2 → Eg := fun _ => 1




def lG : Submodule Eg (Fin 2 → Eg) := Submodule.span Eg {v0}



def muG : Measure (archUnitary hG vG) := Measure.haar

instance : muG.IsHaarMeasure := by
  unfold muG
  infer_instance

theorem re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast



theorem vecAt_apply (x : Fin 2 → Eg) (w : InfinitePlace Eg) (i : Fin 2) :
    vecAt vG x w i = w.embedding (x i) := by
  simp [vecAt, vG]


def Bm : Matrix (Fin 2) (Fin 2) ℂ := !![5 / 4, 3 / 4; 3 / 4, 5 / 4]

theorem det_Bm : Bm.det = 1 := by
  simp [Bm, Matrix.det_fin_two]
  norm_num

def gBu : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm (by rw [det_Bm]; norm_num)

def gB : archUnitary hG vG :=
  ⟨fun _ => gBu, mem_archUnitary.2 fun w => by
    rw [gramAt_hG]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gBu, Bm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, map_ofNat] <;> norm_num⟩



def e0 : Fin 2 → Eg := Pi.single 0 1



theorem unitaryTransvection_zero_first_mem_closure : e0 ∈ LaG := single_mem_LaG 0

theorem first_basis_ne_zero : e0 ≠ 0 := fun h => by
  have := congrFun h 0
  simp [e0] at this


def VVG : Set (Fin 2 → Eg) := {y | ∃ γ ∈ latticeStab hG LaG, γ • v0 = y}






end

end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
