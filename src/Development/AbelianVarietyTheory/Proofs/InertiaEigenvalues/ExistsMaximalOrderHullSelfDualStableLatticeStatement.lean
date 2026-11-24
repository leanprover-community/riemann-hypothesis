module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMaximalOrderHullSelfDualStableLattice
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

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x, (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) → ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧ (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧ (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by
  first | exact @GlobalTheory.HullLat.exists_hull | exact GlobalTheory.HullLat.exists_hull | (intros; apply GlobalTheory.HullLat.exists_hull <;> assumption)
