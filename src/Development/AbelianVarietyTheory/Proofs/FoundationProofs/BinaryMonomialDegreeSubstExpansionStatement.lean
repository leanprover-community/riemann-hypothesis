module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
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

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.binaryMonomialDegree_subst_expansion : ∀ (R : Type) [CommRing R] (w : ℕ), (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (k : Fin (w + 1)), slP m (mon R w k) = ∑ i, MvPolynomial.C ((cf w m i k : ℤ) : R) * mon R w i) ∧ (∀ p : MvPolynomial (Fin 2) R, p.IsHomogeneous w → p = ∑ i : Fin (w + 1), MvPolynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) * mon R w i) ∧ (∀ i, (mon R w i).IsHomogeneous w) ∧ (∀ (u : Fin 2 → R) (i : Fin (w + 1)), MvPolynomial.eval u (mon R w i) = u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) ∧ (∀ c : Fin (w + 1) → R, ∑ i, MvPolynomial.C (c i) * mon R w i = 0 → c = 0) := by
  first | exact @GlobalTheory.KZ.H3.mon_expand | exact GlobalTheory.KZ.H3.mon_expand | (intros; apply GlobalTheory.KZ.H3.mon_expand <;> assumption)
