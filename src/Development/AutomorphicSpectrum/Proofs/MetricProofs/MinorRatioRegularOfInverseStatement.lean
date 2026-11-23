module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfInverse
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

open Matrix

theorem _root_.GlobalTheory.T.minor_ratio_regular_of_inverse : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (n r : ℕ) (Fm : Matrix (Fin n) (Fin r) Φ) (U : Matrix (Fin r) (Fin r) Φ) (C : Matrix (Fin r) (Fin n) Φ) (X : Φ), U.BlockTriangular id → (∀ a b, (Fm * U) a b / X ∈ R) → (∀ a b, C a b ∈ R) → (∀ a b, ∑ k, C a k * ((Fm * U) k b / X) = if a = b then 1 else 0) → ∀ (a : ℕ) (ha : a ≤ r) (J₀ : Fin a → Fin n), (Fm.submatrix J₀ (Fin.castLE ha)).det ≠ 0 → (∀ J : Fin a → Fin n, (Fm.submatrix J (Fin.castLE ha)).det / (Fm.submatrix J₀ (Fin.castLE ha)).det ∈ R) → (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ∈ R ∧ ((∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a)⁻¹ ∈ R ∧ (∏ l : Fin a, U (Fin.castLE ha l) (Fin.castLE ha l)) * (Fm.submatrix J₀ (Fin.castLE ha)).det / X ^ a ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.UnitMinor.unit_minor | exact GlobalTheory.CompanionTheory.Metric.UnitMinor.unit_minor | (intros; apply GlobalTheory.CompanionTheory.Metric.UnitMinor.unit_minor <;> assumption)
