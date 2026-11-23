module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSq
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem _root_.GlobalTheory.T.hodge_tate_constant_divides_p_sq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp | exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp <;> assumption)
