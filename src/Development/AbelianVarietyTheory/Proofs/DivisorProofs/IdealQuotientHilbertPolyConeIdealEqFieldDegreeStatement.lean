module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
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

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree : ∀ (K : Type) [Field K] (N : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 → GlobalTheory.idealHilbertPoly (coneIdeal K y) = Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  first | exact @GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | exact GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | (intros; apply GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin <;> assumption)
