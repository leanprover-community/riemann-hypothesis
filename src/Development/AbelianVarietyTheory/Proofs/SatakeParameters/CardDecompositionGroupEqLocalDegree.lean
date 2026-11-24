module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.KrullDimension.PID
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.DecompCard

theorem card_stabilizer_eq_locDeg : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (v w : HeightOneSpectrum (𝓞 E)), v ∈ placesOver E l → w ∈ placesOver E l →
    Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) = locDeg E w := by
  intro l _ E _ _ _ v w hv hw
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpz.ne_zero).2 hpz
  have := v.isPrime
  have := w.isPrime
  have hover : ∀ R : HeightOneSpectrum (𝓞 E), R ∈ placesOver E l →
      R.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := fun R hR =>
    (Ideal.liesOver_span_iff R.isPrime.ne_top hpz).mpr (by simpa [placesOver] using hR)
  have := hover v hv
  have := hover w hw
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[ℚ] E) (Ideal.span {(l : ℤ)}) v.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal (E ≃ₐ[ℚ] E), locDeg]

end GlobalTheory.DecompCard
