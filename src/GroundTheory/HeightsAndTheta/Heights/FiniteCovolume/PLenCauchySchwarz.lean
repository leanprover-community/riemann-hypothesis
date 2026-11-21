import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLenCauchySchwarz
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem LenSq.re_nonneg {P : Matrix ι ι ℂ} (hP : P.PosDef) (y : ι → ℂ) :
    0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re :=
  (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem LenSq.proof (h : HermitianForm F E W) (v : Basis ι E W) : LenSq.Statement h v := by
  intro M y
  have hw : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
    LenSq.re_nonneg (M.posDef w) (y w)
  refine ⟨hw, ?_⟩
  unfold Majorant.len
  exact Real.sq_sqrt (Finset.sum_nonneg fun w _ => hw w)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

theorem majorant_mul_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) : H * P⁻¹ * H = P := by
  obtain ⟨hP, -, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  calc H * P⁻¹ * H = (P * H⁻¹ * P) * P⁻¹ * H := by rw [hPHP]
    _ = P * H⁻¹ * (P * P⁻¹) * H := by simp only [Matrix.mul_assoc]
    _ = P := by
      rw [Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

theorem MajorantBound.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MajorantBound.Statement ι := by
  intro H P hM z
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set w := P⁻¹ *ᵥ (H *ᵥ z) with hw
  have h1 : P *ᵥ w = H *ᵥ z := by
    rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star w ⬝ᵥ (P *ᵥ w) = star z ⬝ᵥ (P *ᵥ z) := by
    rw [h1, hw, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) z w
  have e1 : (inner ℂ z w : ℂ) = star z ⬝ᵥ (H *ᵥ z) := by
    change (P *ᵥ w) ⬝ᵥ star z = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ w z : ℂ) = star (star z ⬝ᵥ (H *ᵥ z)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) w z).symm
  have e3 : (inner ℂ z z : ℂ) = star z ⬝ᵥ (P *ᵥ z) := by
    change (P *ᵥ z) ⬝ᵥ star z = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ w w : ℂ) = star z ⬝ᵥ (P *ᵥ z) := by
    change (P *ᵥ w) ⬝ᵥ star w = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  have hnn : 0 ≤ (star z ⬝ᵥ (P *ᵥ z)).re := hP.posSemidef.re_dotProduct_nonneg z
  have hn : 0 ≤ ‖star z ⬝ᵥ (H *ᵥ z)‖ := norm_nonneg _
  simp only [RCLike.re_to_complex] at cs
  nlinarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

theorem majorant_cauchySchwarz {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (H *ᵥ b)‖ ≤
      Real.sqrt (star a ⬝ᵥ (P *ᵥ a)).re * Real.sqrt (star b ⬝ᵥ (P *ᵥ b)).re := by
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set c := P⁻¹ *ᵥ (H *ᵥ b) with hc
  have h1 : P *ᵥ c = H *ᵥ b := by
    rw [hc, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star c ⬝ᵥ (P *ᵥ c) = star b ⬝ᵥ (P *ᵥ b) := by
    rw [h1, hc, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) a c
  have e1 : (inner ℂ a c : ℂ) = star a ⬝ᵥ (H *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star a = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ c a : ℂ) = star (star a ⬝ᵥ (H *ᵥ b)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) c a).symm
  have e3 : (inner ℂ a a : ℂ) = star a ⬝ᵥ (P *ᵥ a) := by
    change (P *ᵥ a) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ c c : ℂ) = star b ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star c = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  simp only [RCLike.re_to_complex] at cs
  have ha : 0 ≤ (star a ⬝ᵥ (P *ᵥ a)).re := hP.posSemidef.re_dotProduct_nonneg a
  have hb : 0 ≤ (star b ⬝ᵥ (P *ᵥ b)).re := hP.posSemidef.re_dotProduct_nonneg b
  rw [← Real.sqrt_mul ha]
  exact Real.le_sqrt_of_sq_le (by nlinarith)

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Majorant.isMajorantOf {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (w : InfinitePlace E) : IsMajorantOf (gramAt h v w) (M.P w) :=
  ⟨M.posDef w, (GramAtData.proof h v w).1, (GramAtData.proof h v w).2, M.siegel w⟩

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem Majorant.sqrt_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    Real.sqrt (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re ≤ M.len y := by
  unfold Majorant.len
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re)
    (fun u _ => LenSq.re_nonneg (M.posDef u) (y u)) (Finset.mem_univ w))

theorem LenCauchySchwarz.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LenCauchySchwarz.Statement h v := by
  intro M g x y w
  rw [HermAtPlace.proof h v w x y, ← ArchInvariant.proof h v g (vecAt v x) (vecAt v y) w]
  refine (majorant_cauchySchwarz (M.isMajorantOf w) _ _).trans ?_
  exact mul_le_mul (M.sqrt_le_len _ w) (M.sqrt_le_len _ w) (Real.sqrt_nonneg _)
    ((Real.sqrt_nonneg _).trans (M.sqrt_le_len _ w))

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
