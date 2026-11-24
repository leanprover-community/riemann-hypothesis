module

public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventually
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).host.q : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧ ((Fm.D x a).host.d : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧
      ∀ p ∈ (Fm.D x a).host.small, (p : ℝ) < LevelStarExponents.lStar (Fm.L x a) := by
  first | exact @GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar | exact GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar | (intros; apply GlobalTheory.LevelBelowStarBound.QdSmall.qd_lt_lStar <;> assumption)
