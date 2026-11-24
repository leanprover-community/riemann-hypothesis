module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuadCharOfOfIsNormChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormRam
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.ConvolutionTheory.Sph

private theorem one_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hp : (Module.finrank K M).Prime) (w : HeightOneSpectrum (𝓞 M))
    (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 ∧ ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard = 1 := by
  have := w.isPrime
  haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
  have k := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under (𝓞 K)) (𝓞 M) Gal(M/K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(M/K), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K),
    IsGalois.card_aut_eq_finrank] at k
  have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := fun h => hram (Ideal.ramificationIdx_eq_one_iff.1 h)
  have hd : w.asIdeal.ramificationIdx (𝓞 K) ∣ Module.finrank K M :=
    ⟨((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K), by rw [← k]; ring⟩
  have hel := (Nat.dvd_prime hp).1 hd |>.resolve_left he
  rw [hel] at k
  have h1 : ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    calc Module.finrank K M * (((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K))
        = ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * (Module.finrank K M * w.asIdeal.inertiaDeg (𝓞 K)) := by ring
      _ = Module.finrank K M * 1 := by rw [k, mul_one]
  exact ⟨Nat.eq_one_of_mul_eq_one_left h1, Nat.eq_one_of_mul_eq_one_right h1⟩

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.normRam :
    UpperTheory.ConvolutionTheory.Sph.NormRam := by
  intro K M _ _ _ _ _ _ hp w hram
  obtain ⟨hf, hg⟩ := one_of_ramified hp w hram
  refine ⟨?_, fun w' hw' => ?_, fun η hη hu => ?_⟩
  · have h := GlobalTheory.QuadNormChar.normV_under (K := K) w
    rwa [hf, pow_one] at h
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hg
    have h1 : w.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) := ⟨w.isPrime, ⟨rfl⟩⟩
    have h2 : w'.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) :=
      ⟨w'.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw'.symm⟩⟩
    rw [ha] at h1 h2
    exact HeightOneSpectrum.ext (h2.trans h1.symm)
  · let Ω := AlgebraicClosure M
    haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
    haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
    haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
    have hAv : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hA (algebraMap (𝓞 K) (𝓞 M) x)
    have hmove : ∃ s ∈ Ine (F := K) A, ¬ UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes M s := by
      by_contra hfix
      push_neg at hfix
      obtain ⟨hlo, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 K)) w hAv hA hfix
      exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
    exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam K M Ω hp η hη A _ hAv hmove hu
