module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalenceStatement
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

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKMid.Pair.mk_eq_iff_rel_and_out_rel :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G),
      (Quot.mk Pair.Rel P = Quot.mk Pair.Rel Q ↔ P.Rel Q) ∧
        (Quot.out (Quot.mk Pair.Rel P : Cls G)).Rel P := by
  intro p _ G P Q
  have e : Equivalence (Pair.Rel (G := G)) := GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence p G
  have key : ∀ A B : Pair G, (Quot.mk Pair.Rel A = Quot.mk Pair.Rel B ↔ A.Rel B) := by
    intro A B
    rw [Quot.eq, e.eqvGen_iff]
  refine ⟨key P Q, ?_⟩
  exact (key _ _).1 (Quot.out_eq _)
