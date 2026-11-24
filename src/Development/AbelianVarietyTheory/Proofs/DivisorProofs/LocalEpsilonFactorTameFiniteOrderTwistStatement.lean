module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps

theorem _root_.GlobalTheory.T.localEpsilonFactor_tame_finiteOrder_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  first | exact @GlobalTheory.TameTwistEps.locEps_tame_twist | exact GlobalTheory.TameTwistEps.locEps_tame_twist | (intros; apply GlobalTheory.TameTwistEps.locEps_tame_twist <;> assumption)
