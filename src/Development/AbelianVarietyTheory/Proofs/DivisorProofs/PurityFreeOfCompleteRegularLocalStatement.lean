module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFreeOfCompleteRegularLocal
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

open IsLocalRing

theorem _root_.GlobalTheory.T.purityFree_of_complete_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], (∀ (S : Type) [CommRing S] [IsRegularLocalRing S], IsAdicComplete (maximalIdeal S) S → ringKrullDim S = ringKrullDim R → GlobalTheory.PurityFree S) → GlobalTheory.PurityFree R := by
  first | exact @GlobalTheory.PurityStep.purityFree_of_complete | exact GlobalTheory.PurityStep.purityFree_of_complete | (intros; apply GlobalTheory.PurityStep.purityFree_of_complete <;> assumption)
