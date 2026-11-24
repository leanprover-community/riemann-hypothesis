module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHSiegelOperator
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), IsSB φ → IsSB (dropF φ) ∧ ∀ Z ∈ Hn Ψ (N + 1), dropZ Ψ Z ∈ Hn Ψ N ∧ (∀ t : ℝ, 0 ≤ t → pushZ Ψ Z (Pi.single 0 1) t ∈ Hn Ψ (N + 1)) ∧ ∀ z z' : CM Ψ n (N + 1), Tendsto (fun t : ℝ => thH Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) z z') atTop (𝓝 (thH Ψ (dropF φ) (dropZ Ψ Z) (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by
  first | exact @GlobalTheory.SW.thH_siegel_operator | exact GlobalTheory.SW.thH_siegel_operator | (intros; apply GlobalTheory.SW.thH_siegel_operator <;> assumption)
