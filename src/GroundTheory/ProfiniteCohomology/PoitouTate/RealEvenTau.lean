module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenFree
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealEvenLevel
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInputs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
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

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  [Fintype S] {N : ℕ} [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (hev : Even N)

def GsTauBijective (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) : Prop :=
  letI : IsDiscreteRep (gsRoots S N) := isDiscreteRep_gsRoots S N
  letI := isDiscreteRep_res_subtype (gsRoots S N) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
  ∀ τ : compactCohomologyRes (mackeyFamily U (gsFinFamily S ιs))
      (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) 3 →+ ZMod N,
    Function.Surjective τ → ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective (compactZmodDualityMap (mackeyFamily U (gsFinFamily S ιs))
        (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S N)) (nsmul_gsRoots S N) τ h)



include hS hev in
theorem gsTauBijective_gsOpenSubgroup {L : FiniteSubfield} [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ (2 * N) = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (hU : gsOpenSubgroup S hL ≤ W₀) : GsTauBijective S ιs (N := N) (gsOpenSubgroup S hL) := by
  intro τ hτ r s h
  have hTC := isTotallyComplex_of_gsOpenSubgroup_le S hS hev hL W₀ hW₀ hU
  let := fintypePlacesOver (L := L) S
  have : Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
    nonempty_placesOver_of_natCast_mem S Nat.prime_two (mem_of_natCast_two_mem_of_even S hS hev)
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((N : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  -- The conclusion converts to the goal without unfolding the cohomology constructions.
  with_reducible
    exact bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective S ιs hL N τ hτ _
      (gsLevelBijective_gsCompactInv (placesOver S) (gsMackeyEmbeddings hL ιs) hSL (Or.inr hTC)) h

end GroundTheory.ProfCoh
