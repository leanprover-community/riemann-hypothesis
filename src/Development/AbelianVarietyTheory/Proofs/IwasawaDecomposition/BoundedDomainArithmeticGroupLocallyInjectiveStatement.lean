module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjective
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  first | exact @GlobalTheory.LocInj.locInj | exact GlobalTheory.LocInj.locInj | (intros; apply GlobalTheory.LocInj.locInj <;> assumption)
