module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.hermitianHeisenbergOperator_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsSB (heisH d b φ) ∧ (∀ Z ∈ Hn Ψ N, ∀ z z' : CM Ψ n N, thH Ψ (heisH d b φ) Z z z' = cexp (2 * π * I * expo Ψ d Z z z' + π * I * ((Algebra.trace ℚ E (∑ k, ∑ a, b k a * cc (d k a)) : ℚ) : ℂ)) * thH Ψ φ Z (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ)) ∧ ∀ γ ∈ UU E N, weil Ψ γ (heisH d b φ) = heisH (Matrix.fromCols d b * γ⁻¹).toCols₁ (Matrix.fromCols d b * γ⁻¹).toCols₂ (weil Ψ γ φ) := by
  first | exact @GlobalTheory.SW.heisH_laws | exact GlobalTheory.SW.heisH_laws | (intros; apply GlobalTheory.SW.heisH_laws <;> assumption)
