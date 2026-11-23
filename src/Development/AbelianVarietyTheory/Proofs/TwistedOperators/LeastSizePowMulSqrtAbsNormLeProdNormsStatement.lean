module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNorms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

theorem _root_.GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  first | exact @GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | exact GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | (intros; apply GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod <;> assumption)
