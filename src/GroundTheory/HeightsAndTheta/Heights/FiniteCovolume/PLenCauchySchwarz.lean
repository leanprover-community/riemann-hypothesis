module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StLenCauchySchwarz
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenSq
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Majorant.isMajorantOf {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (w : InfinitePlace E) : IsMajorantOf (gramAt h v w) (M.P w) :=
  ⟨M.posDef w, (GramAtData.proof h v w).1, (GramAtData.proof h v w).2, M.siegel w⟩


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
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
