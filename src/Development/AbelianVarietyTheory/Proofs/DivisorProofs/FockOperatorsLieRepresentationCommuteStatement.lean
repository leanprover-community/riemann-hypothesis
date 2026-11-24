module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockOperators_lie_representation_commute : ∀ (p q r s : ℕ), (∀ Y Z, omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y) ∧ IsLieAct (fockAct1 p q r s) ∧ IsLieAct (fockAct2 p q r s) ∧ ∀ Y Z, fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  first | exact @GlobalTheory.FockAlg.fock_lie_and_commute | exact GlobalTheory.FockAlg.fock_lie_and_commute | (intros; apply GlobalTheory.FockAlg.fock_lie_and_commute <;> assumption)
