module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerDifferentialsSpanLocal
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

open MvPolynomial

theorem _root_.GlobalTheory.T.kaehler_differentials_span_local : ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | exact GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D | (intros; apply GlobalTheory.CompanionTheory.Kaehler.maximalIdeal_eq_span_of_span_D <;> assumption)
