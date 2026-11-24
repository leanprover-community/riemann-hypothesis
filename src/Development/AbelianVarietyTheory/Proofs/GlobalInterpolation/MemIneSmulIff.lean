module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
public import ReciprocityTheory.GaloisValuations.ArithOfA

@[expose] public section

open NumberField IsDedekindDomain Pointwise

namespace GlobalTheory.PlaceConjQ

theorem eq_of_prime_mem {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have : Fact q.Prime := ⟨hq⟩
  have := v.isPrime
  have := w.isPrime
  have h1 := ((ReciprocityTheory.Gal.liesOver_span_iff q v.asIdeal).2 hv).over
  have h2 := ((ReciprocityTheory.Gal.liesOver_span_iff q w.asIdeal).2 hw).over
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  have e : Rat.ringOfIntegersEquiv.symm n = algebraMap ℤ (𝓞 ℚ) n :=
    (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n).trans (eq_intCast (algebraMap ℤ (𝓞 ℚ)) n).symm
  rw [e, ← Ideal.mem_comap, ← Ideal.mem_comap]
  change n ∈ v.asIdeal.under ℤ ↔ n ∈ w.asIdeal.under ℤ
  rw [← h1, ← h2]

end GlobalTheory.PlaceConjQ
