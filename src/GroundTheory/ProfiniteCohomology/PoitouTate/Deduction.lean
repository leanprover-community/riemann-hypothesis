module

public import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
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
public import GroundTheory.ProfiniteCohomology.PoincarePairs.IsDiscreteRepResHomCoindRes
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)
  (H : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)


omit [Fintype S] [NeZero N] in
instance isDiscreteRep_dualRep_gsRoots : IsDiscreteRep (dualRep (gsRoots S N) M) :=
  isDiscreteRep_dualRep (gsRoots S N) M




end GroundTheory.ProfCoh
