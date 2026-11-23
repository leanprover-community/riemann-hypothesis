module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLine
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

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

theorem _root_.GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  first | exact @GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | exact GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | (intros; apply GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line <;> assumption)
