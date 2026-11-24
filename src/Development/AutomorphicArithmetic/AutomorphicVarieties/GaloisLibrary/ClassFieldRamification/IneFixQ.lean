module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.ineFixQ :
    ∀ (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsGalois ℚ K] [IsGalois ℚ H] (p : ℕ), p.Prime → (UnramAt K p ↔ ∀ w : HeightOneSpectrum (𝓞 H), (p : 𝓞 H) ∈ w.asIdeal → w.asIdeal.inertia Gal(H/ℚ) ≤ (resTo ℚ K H).ker) := by
  intro K H _ _ _ _ _ _ _ p hp
  rw [UpperTheory.V.CF.unramIff.1 K p hp]
  constructor
  · intro h w hw
    have hv : (p : 𝓞 K) ∈ w.asIdeal.under (𝓞 K) := by
      simpa [Ideal.under, Ideal.mem_comap, map_natCast] using hw
    let v : HeightOneSpectrum (𝓞 K) := ⟨w.asIdeal.under (𝓞 K), inferInstance, fun hb => by
      rw [hb] at hv
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hv)⟩
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w]
    exact h v hv
  · intro h v hv
    have hle : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ ≤ v.asIdeal := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 H) (by rw [hx, map_zero])
      rw [hx0]
      exact v.asIdeal.zero_mem
    obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal ⊥ hle
    have hpQ : (p : 𝓞 H) ∈ Q := by
      have hc : (p : 𝓞 K) ∈ Q.comap (algebraMap (𝓞 K) (𝓞 H)) := by
        change (p : 𝓞 K) ∈ Ideal.under (𝓞 K) Q
        rw [hQv]
        exact hv
      simpa [Ideal.mem_comap, map_natCast] using hc
    let w : HeightOneSpectrum (𝓞 H) := ⟨Q, hQ, fun hb => by
      rw [hb] at hpQ
      exact (Nat.cast_ne_zero.mpr hp.ne_zero) ((Ideal.mem_bot).mp hpQ)⟩
    have h1 := h w hpQ
    rw [← Subgroup.map_eq_bot_iff, UpperTheory.V.CF.ineMap ℚ K H w] at h1
    have hw : Ideal.under (𝓞 K) w.asIdeal = v.asIdeal := hQv
    rwa [hw] at h1
