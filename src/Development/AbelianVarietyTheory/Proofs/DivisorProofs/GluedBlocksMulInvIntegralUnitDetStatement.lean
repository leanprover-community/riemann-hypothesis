module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedBlocksMulInvIntegralUnitDet
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

theorem _root_.GlobalTheory.T.glued_blocks_mul_inv_integral_unit_det : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (ι : Type) (lab : Fin d → ι)
    (S : ι → Finset (Fin d)) (x y : ι → Matrix (Fin d) (Fin d) C),
    (∀ i a, a ∈ S i → lab a = i) →
    (∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) → (∀ i a b, y i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) →
    (∀ i a b, IsIntV v (x i a b)) → (∀ i a b, IsIntV v (y i a b)) →
    (∀ i a c, a ∈ S i → c ∈ S i → ∑ b, x i a b * y i b c = if a = c then 1 else 0) →
    (∀ a b, IsIntV v (glue lab S x a b)) ∧ glue lab S x * glue lab S y = 1 ∧
      v (glue lab S x).det = 0 := by
  first | exact @GlobalTheory.GlueBlocks.glue_mul_glue_inv | exact GlobalTheory.GlueBlocks.glue_mul_glue_inv | (intros; apply GlobalTheory.GlueBlocks.glue_mul_glue_inv <;> assumption)
