module

public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.psiCoord_exists_unique_up_to_unit_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (Dg : DegData R (maximalIdeal R)), IsIntegrallyClosed R → ∀ χ, (∃ r, PsiCoord Dg.toPre χ r ∧ r ≠ 0 ∧ (χ ≠ 0 → r ∈ maximalIdeal R) ∧ (χ = 0 → IsUnit r)) ∧ (∀ r r', PsiCoord Dg.toPre χ r → PsiCoord Dg.toPre χ r' → ∃ u : Rˣ, r' = u * r) ∧ ∀ (W : Set (Sp R)) (𝔭 : PrimeSpectrum R), IsOpen W → 𝔭 ∈ W → PsiUnitOn Dg.toPre χ W → ∀ r, PsiCoord Dg.toPre χ r → r ∉ 𝔭.asIdeal := by
  first | exact @GlobalTheory.PsiCoordLocal.main | exact GlobalTheory.PsiCoordLocal.main | (intros; apply GlobalTheory.PsiCoordLocal.main <;> assumption)
