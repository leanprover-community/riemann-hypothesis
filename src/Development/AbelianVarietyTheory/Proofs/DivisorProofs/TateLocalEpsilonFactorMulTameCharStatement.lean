module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameChar
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

theorem _root_.GlobalTheory.T.tateLocalEpsilonFactor_mul_tameChar : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) (s : ℂ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → (q : 𝓞 E) ∉ w.asIdeal ^ 2 → ExpAt χ w 2 → ξ.TameAt w → ExpAt (χ * ξ) w 2 ∧ ∃ y : Eˣ, locEps (χ * ξ) w 2 s = ((ξ.locK w y : ℂˣ) : ℂ) * locEps χ w 2 s := by
  first | exact @GlobalTheory.TameTwist.locEps_mul_tame | exact GlobalTheory.TameTwist.locEps_mul_tame | (intros; apply GlobalTheory.TameTwist.locEps_mul_tame <;> assumption)
