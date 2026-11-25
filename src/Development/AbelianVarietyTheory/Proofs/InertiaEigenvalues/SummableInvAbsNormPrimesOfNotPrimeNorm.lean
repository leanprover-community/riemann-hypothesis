module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import GroundTheory.GlobalFields.TateThesis.DegreeOnePrimes

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory

theorem summable_inv_absNorm_of_not_prime :
    ∀ (K : Type) [Field K] [NumberField K],
      Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} =>
        ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  intro K _ _
  simpa only [Real.rpow_neg_one] using
    (GroundTheory.Global.summable_absNorm_rpow_neg_of_not_prime (L := K) (s := 1)
      one_half_lt_one)

end GlobalTheory
