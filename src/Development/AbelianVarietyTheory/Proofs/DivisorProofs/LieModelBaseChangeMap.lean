module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiInvariantTestFunctionSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentSumEqZeroOfOrbitalIntegralEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceDefiniteFormEqSumConjClassesStatement
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

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem trace_definite_forms_identity : TraceDefinitePairsEqAutomorphicTrace := by
  intro p _ G ha V _ _ _ ξ wt hξ L f hf hfb K' f' hf' hf'b hvan
  rw [GlobalTheory.T.bi_invariant_test_function_sum p G ha wt L f hf hfb K' f' hf' hf'b]
  unfold dTrace
  refine finsum_congr (fun q => ?_)
  rw [GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses p G ha V ξ L f hf hfb K' f' hf' hf'b (Quot.out q)]
  refine finsum_congr (fun c => ?_)
  split_ifs with h
  · rw [hξ (Quot.out q) (Quotient.out c) h.1 h.2.1]
  · rw [GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero p G ha L f hf hfb K' f' hf' hf'b (Quot.out q) (Quotient.out c)
      (hvan (Quot.out q) _ _ _ (Quotient.out c) h), mul_zero]

end GlobalTheory.LKDef
