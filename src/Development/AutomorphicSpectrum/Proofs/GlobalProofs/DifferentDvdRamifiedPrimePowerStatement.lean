module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePower
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.different_dvd_ramified_prime_power : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 → (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) → differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  first | exact @GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | exact GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | (intros; apply GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow <;> assumption)
