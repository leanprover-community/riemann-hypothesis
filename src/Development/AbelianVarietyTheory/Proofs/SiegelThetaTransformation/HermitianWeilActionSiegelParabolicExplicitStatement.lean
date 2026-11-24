module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicit
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
open scoped ComplexConjugate ComplexOrder Real

theorem _root_.GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → (∀ γ ∈ UU E N, γ.toBlocks₂₁ = 0 → ∀ x, weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * chiH Ψ (-(γ.toBlocks₁₂ * ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ UU E N, ∀ γ' ∈ UU E N, botSpan γ = botSpan γ' → ∀ Z ∈ Hn Ψ N, ∀ z z', eisTerm Ψ γ φ Z z z' = eisTerm Ψ γ' φ Z z z' := by
  first | exact @GlobalTheory.SW.weil_parabolic | exact GlobalTheory.SW.weil_parabolic | (intros; apply GlobalTheory.SW.weil_parabolic <;> assumption)
