module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearity
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
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.siegelWeilDifference_automorphy_linearity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M : ℕ) (φ : Fam E n N), 0 < M → (∀ Λ ∈ Vset E n M, IsSB (φ Λ)) → ∀ Z ∈ Hn Ψ N, (∀ γ ∈ UU E N, swd Ψ M (fun Λ => weil Ψ γ (φ Λ)) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * swd Ψ M φ Z 0 0) ∧ (∀ β : Matrix (Fin N) (Fin N) E, ccT β = β → swd Ψ M (fun Λ x => chiH Ψ β x * φ Λ x) Z 0 0 = swd Ψ M φ (fun τ => Z τ + β.map τ.1) 0 0) ∧ (∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → swd Ψ M (φ + ψ) Z 0 0 = swd Ψ M φ Z 0 0 + swd Ψ M ψ Z 0 0) ∧ (∀ c : ℂ, swd Ψ M (c • φ) Z 0 0 = c * swd Ψ M φ Z 0 0) ∧ ∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, ψ Λ = φ Λ) → swd Ψ M ψ Z 0 0 = swd Ψ M φ Z 0 0 := by
  first | exact @GlobalTheory.SW.swd_automorphy_linear | exact GlobalTheory.SW.swd_automorphy_linear | (intros; apply GlobalTheory.SW.swd_automorphy_linear <;> assumption)
