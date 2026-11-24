module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThree
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

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (X : Data E r), 3 ≤ M → (∀ γ, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDet.det_eq_one | exact GlobalTheory.UnitaryCongruenceDet.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDet.det_eq_one <;> assumption)
