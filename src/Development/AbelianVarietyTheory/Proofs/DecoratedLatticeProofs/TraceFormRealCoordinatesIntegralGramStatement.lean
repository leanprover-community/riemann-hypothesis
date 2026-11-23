module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.traceForm_real_coordinates_integral_gram : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)), IsRealCoord I ρ → ∃ (X : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (c : ℕ), μ ≠ 0 ∧ 1 ≤ c ∧ ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ B B' : Matrix (Fin N) (Fin N) ℤ, B.map (Int.cast : ℤ → ℝ) = (gm I ρ y e)ᵀ * X * gm I ρ y e ∧ gm I ρ y e * B'.map (Int.cast : ℤ → ℝ) * (gm I ρ y e)ᵀ = μ • X ∧ ∀ i j, (B i j : ℚ) = c * trForm I (e i) (e j) := by
  first | exact @GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | exact GlobalTheory.CuspGeo.TrReal.trace_form_real_coord | (intros; apply GlobalTheory.CuspGeo.TrReal.trace_form_real_coord <;> assumption)
