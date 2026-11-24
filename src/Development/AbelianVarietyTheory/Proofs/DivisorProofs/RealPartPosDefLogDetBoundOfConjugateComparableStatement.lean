module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPartPosDefLogDetBoundOfConjugateComparable
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

theorem _root_.GlobalTheory.T.realPart_posDef_logDet_bound_of_conjugate_comparable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (κ : ℝ), G.PosDef → 1 ≤ κ → (∀ c : ι → ℂ, (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j).re ≤ κ * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j).re) → (G.map Complex.re).PosDef ∧ |Real.log (G.map Complex.re).det - Real.log G.det.re| ≤ Fintype.card ι * Real.log (2 * κ) := by
  first | exact @GlobalTheory.RealPartDet.main | exact GlobalTheory.RealPartDet.main | (intros; apply GlobalTheory.RealPartDet.main <;> assumption)
