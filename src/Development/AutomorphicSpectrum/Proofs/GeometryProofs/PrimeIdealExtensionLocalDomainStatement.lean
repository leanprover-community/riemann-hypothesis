module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIdealExtensionLocalDomain
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


theorem _root_.GlobalTheory.T.prime_ideal_extension_local_domain : ∀ (R B : Type) [CommRing R] [IsDedekindDomain R] [CommRing B] [IsDomain B] [IsNoetherianRing B] (u : R →+* B), u.FiniteType → (∀ p : Ideal R, p.IsMaximal → ∀ a b : B, a * b ∈ p.map u → a ∈ p.map u ∨ b ∈ p.map u) → ∀ (f : B) (d : R), d ≠ 0 → (∀ m : Ideal B, m.IsMaximal → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : B →+* O), (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧ Function.Injective (ψ.comp u) ∧ ∃ c, ψ f = ψ (u d) * c) → ∃ a, f = u d * a := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | exact GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local | (intros; apply GlobalTheory.CompanionTheory.Ggeo.RegularDvd.dvd_of_local <;> assumption)
