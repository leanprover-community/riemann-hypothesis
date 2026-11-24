module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelOneTwelveMulFinrankModularFormLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

theorem _root_.GlobalTheory.T.levelOne_twelve_mul_finrank_modularForm_lower_bound : ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) + 4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤ 12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  first | exact @GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | exact GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound | (intros; apply GlobalTheory.OddFrame.levelOne_twelve_mul_finrank_lower_bound <;> assumption)
