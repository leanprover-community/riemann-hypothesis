module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticSimilitudeInvertibleModN
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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.symplecticSimilitude_invertible_modN : ∀ (h N m : ℕ) (T : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ)), N ≠ 0 → m.Coprime N → (∀ x y, omegaStd (T x) (T y) ≡ m * omegaStd x y [ZMOD N]) → (∀ a, (∃ b, T a = N • b) → ∃ b, a = N • b) ∧ (∀ a, ∃ a' b, T a' = a + N • b) ∧ ∃ T' : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ), (∀ x, ∃ b, T (T' x) = x + N • b) ∧ ∀ m' : ℕ, m * m' ≡ 1 [MOD N] → ∀ x y, omegaStd (T' x) (T' y) ≡ m' * omegaStd x y [ZMOD N] := by
  first | exact @GlobalTheory.SympModN.symplecticSimilitude_modN | exact GlobalTheory.SympModN.symplecticSimilitude_modN | (intros; apply GlobalTheory.SympModN.symplecticSimilitude_modN <;> assumption)
