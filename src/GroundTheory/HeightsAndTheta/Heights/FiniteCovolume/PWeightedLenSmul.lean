module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem WeightedLenSmul.vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i
  simp [vecAt, map_mul]


omit [NumberField F] [IsTotallyReal F] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem WeightedLenSmul.invApply_vecAt_smul {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) (a : E) (x : W) (w : InfinitePlace E) :
    invApply g (vecAt v (a • x)) w = w.embedding a • invApply g (vecAt v x) w := by
  simp only [invApply, WeightedLenSmul.vecAt_smul, Matrix.mulVec_smul]


omit [DecidableEq ι] in
theorem WeightedLenSmul.star_smul_dotProduct_mulVec_smul (P : Matrix ι ι ℂ) (c : ℂ)
    (z : ι → ℂ) :
    star (c • z) ⬝ᵥ (P *ᵥ (c • z)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star z ⬝ᵥ (P *ᵥ z)) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, mul_comm c, Complex.star_def, Complex.conj_mul']
  push_cast
  ring


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem WeightedLenSmul.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LenSq.Statement h v) : WeightedLenSmul.Statement h v := by
  intro M g x a
  rw [(h₁ M _).2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [WeightedLenSmul.invApply_vecAt_smul, WeightedLenSmul.star_smul_dotProduct_mulVec_smul,
    Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
