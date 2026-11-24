module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinWronskianNeZero
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

theorem _root_.GlobalTheory.T.eisenstein_wronskian_ne_zero : ∀ τ : ℍ, 2 * E₄ τ * deriv (⇑E₆ ∘ ofComplex) τ - 3 * E₆ τ * deriv (⇑E₄ ∘ ofComplex) τ ≠ 0 := by
  first | exact @GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | exact GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero | (intros; apply GlobalTheory.EisWronskian.wronskian_E₄_E₆_ne_zero <;> assumption)
