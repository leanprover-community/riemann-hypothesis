module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.PoincarePairs.Natural
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SInvariantToInvariantsEqZeroIff
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n]

theorem pow_notMem_asIdeal_of_forall (ℓ k : ℕ)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    ∀ v ∉ S, (((ℓ ^ k : ℕ) : ℕ) : 𝓞 K.1) ∉ v.asIdeal := fun v hv h => by
  rw [Nat.cast_pow] at h
  exact hv (hS v (v.isPrime.mem_of_pow_mem k h))

variable (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)


include hnS in
theorem nsmul_gsRootsCompact (m : ℕ) (w : gsRootsCompact S ιs n m) : n • w = 0 := by
  obtain ⟨w', rfl⟩ := (bijective_gsRootsComparison S ιs n hnS m).2 w
  rw [← map_nsmul, nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S n) m w', map_zero]

abbrev gsRootsToUnitsCompact (m : ℕ) : gsRootsCompact S ιs n m ⟶ gsUnitsCompact S ιs m :=
  compactCohomologyMap (gsFinFamily S ιs) (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) m

theorem surjective_gsKummerCompactδ (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd ℓ ∨ IsTotallyComplex K.1) :
    Function.Surjective (gsKummerCompactδ S ιs n hnS 1).hom := by
  intro w
  have h0 : (gsRootsToUnitsCompact S ιs n (1 + 1)).hom w = 0 := by
    refine eq_zero_of_gsUnitsCompact_two S ιs ℓ hℓ hS hodd _ k ?_
    rw [← hnk, ← map_nsmul, nsmul_gsRootsCompact S ιs n hnS, map_zero]
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact₁ (gsFinFamily S ιs) (gsKummerLocalMap S ιs n) (gsKummer_shortExact S n hnS)
      (localKummer_shortExact S n) 1) h0

end

end GroundTheory.ProfCoh
