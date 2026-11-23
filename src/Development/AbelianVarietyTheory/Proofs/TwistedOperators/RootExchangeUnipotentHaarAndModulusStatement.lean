module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.rootExchangeUnipotent_haar_and_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure], IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) ∧ IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) ∧ (volN ν n c p).IsHaarMeasure ∧ (volN ν n c p).IsMulRightInvariant ∧ ∀ (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) = (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) • ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  first | exact @GlobalTheory.RootEx.VolN.volN_haar_and_modulus | exact GlobalTheory.RootEx.VolN.volN_haar_and_modulus | (intros; apply GlobalTheory.RootEx.VolN.volN_haar_and_modulus <;> assumption)
