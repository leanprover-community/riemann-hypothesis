module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_transvection_eq_sum : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  first | exact @GlobalTheory.RowSubstTransvection.rowSubst_transvection | exact GlobalTheory.RowSubstTransvection.rowSubst_transvection | (intros; apply GlobalTheory.RowSubstTransvection.rowSubst_transvection <;> assumption)
