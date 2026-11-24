module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGL
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc


theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
