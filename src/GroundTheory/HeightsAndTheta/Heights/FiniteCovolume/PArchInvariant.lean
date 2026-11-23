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
import Mathlib.Tactic.Linter.Style
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

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem star_mulVec_dotProduct_mulVec_mulVec (M H : Matrix ι ι ℂ) (y z : ι → ℂ) :
    star (M *ᵥ y) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star y ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]

theorem ArchInvariant.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchInvariant.Statement h v := by
  intro g y z w
  have hmem := mem_archUnitary.mp (g⁻¹ : archUnitary h v).2 w
  set M : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    with hM
  have hct : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hct] at hmem
  show star (M *ᵥ y w) ⬝ᵥ (gramAt h v w *ᵥ (M *ᵥ z w)) = star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
  rw [star_mulVec_dotProduct_mulVec_mulVec, hmem]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
