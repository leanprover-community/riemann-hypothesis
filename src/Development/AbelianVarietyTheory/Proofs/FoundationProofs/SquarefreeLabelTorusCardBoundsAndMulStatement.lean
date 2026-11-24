module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMul
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

open Polynomial Classical GlobalTheory.BadShare

theorem _root_.GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  first | exact @GlobalTheory.BadShare.torusCard_bounds_mul | exact GlobalTheory.BadShare.torusCard_bounds_mul | (intros; apply GlobalTheory.BadShare.torusCard_bounds_mul <;> assumption)
