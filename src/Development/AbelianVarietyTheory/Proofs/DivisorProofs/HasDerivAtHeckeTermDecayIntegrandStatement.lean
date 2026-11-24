module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntZEqFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeckeTermDecayIntegrand
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

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

theorem _root_.GlobalTheory.T.hasDerivAt_heckeTermDecayIntegrand : ∀ (σ : ℂ) (a : ℤ) (b m : ℕ) (y : ℝ), y ≠ 0 → ∀ t : ℝ,
    HasDerivAt (qZ σ a b m y) (-(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t)) t := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ | exact GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ | (intros; apply GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ <;> assumption)
