module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusDStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponentStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatioStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfieldStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := GlobalTheory.T.conjugateEmbedding_isCMType_sqrtMinusD D.R D.host
  obtain ⟨hκ, hinf⟩ := GlobalTheory.T.one_le_kap_and_lam0_hasInf D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := GlobalTheory.T.lam0_isUnitary_and_trivOnF D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    GlobalTheory.T.isBaseCond_of_split_primes D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact GlobalTheory.T.lam_conductor_exponent D Z hZ l j a P

end GlobalTheory.LamTie
