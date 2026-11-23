module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantBound
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
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.riemann_form_period_determinant : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (A' : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (S : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ), H₁.PosDef → H₂.PosDef → S.det ≠ 0 → Aᵀ * H₁ * A.map star - (A'ᵀ * H₂ * A'.map star)ᵀ = (2 * Complex.I) • S → A * ((Sᵀ)⁻¹ * A'ᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * A'ᵀ).rank = q ∧ ‖(fromRows ((Sᵀ)⁻¹ * A'ᵀ)ᴴ A).det / (((Sᵀ)⁻¹ * A'ᵀ)ᴴ * ((Sᵀ)⁻¹ * A'ᵀ)).det‖ ^ 2 * H₁.det.re = 2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.fcNorm | exact GlobalTheory.CompanionTheory.Ar.Flat.fcNorm | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.fcNorm <;> assumption)
