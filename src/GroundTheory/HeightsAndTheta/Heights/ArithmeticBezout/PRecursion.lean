module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem map_specFirst {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {k n : ℕ}
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    MvPolynomial.map φ (specFirst f u) = specFirst (MvPolynomial.map φ f) (fun j => φ (u j)) := by
  unfold specFirst
  rw [map_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero => simp [specFirstVar]
  | succ i => simp [specFirstVar]

theorem ChowHeightRecursion.proof (hV : ChowFormSectionVertical.Statement) (hA : MahlerSection.Statement)
    (hB : ChowFormBaseChange.Statement) (hAv : BaseChangeAvoid.Statement) :
    ChowHeightRecursion.Statement := by
  intro K _ _ n e δ H I f u hI hf hδ hu
  set u' : Fin n → K := fun j => (u j : K) with hu'
  set g := specFirst f u' with hg

  have hfin_f := log_gaussNorm_support_finite (K := K) hf.1
  have hfin_g : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v g)).Finite := by
    by_cases hg0 : g = 0
    · have : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => Real.log (gaussNorm v g)) = 0 := by
        funext v
        rw [hg0]
        simp [gaussNorm]
        exact Or.inl rfl
      rw [this, Function.support_zero]
      exact Set.finite_empty
    · exact log_gaussNorm_support_finite hg0
  have hfinsum : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g)) + vertTerm I (e + 1) u := by
    unfold vertTerm
    rw [← finsum_add_distrib hfin_g]
    · refine finsum_congr fun v => ?_
      rw [← hV K n e I f u hI hf hu v]
      ring
    · refine Set.Finite.subset (hfin_f.union hfin_g) fun v hv => ?_
      rw [Function.mem_support, ← hV K n e I f u hI hf hu v] at hv
      by_contra hcon
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
      exact hv (by rw [hcon.1, hcon.2, sub_zero])

  have harch : ∀ σ : K →+* ℂ, mahler (H.normAt σ) (e + 1) (f.map σ) =
      mahler (H.normAt σ) e (g.map σ) - δ * (harmonic (n - 1) : ℝ) / 2 -
        cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    intro σ
    obtain ⟨hprime, hcyc⟩ := hB K n (e + 1) I f σ hI hf
    have hδσ : IsMultiHomog δ (MvPolynomial.map σ f) :=
      (isMultiHomog_iff _ _).mpr fun i => IsWeightedHomogeneous.map' ((isMultiHomog_iff _ _).mp hδ i) σ
    have h := hA n e δ (H.normAt σ) _ _ (fun j => σ (u j)) hprime hcyc hδσ
      (fun W hW => hAv K n I u' σ hI hu W hW)
    rw [hg, map_specFirst, h]
    ring
  unfold chowHt
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) (e + 1) (f.map σ) +
        ((e + 1 : ℕ) : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) e (g.map σ) + (e : ℝ) * δ * (harmonic (n - 1) : ℝ) / 2) -
        ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
          (fsLog (H.normAt σ) fun j => σ (u j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [harch σ]
    push_cast
    ring
  rw [hfinsum, hs]
  ring

end

end GroundTheory.Heights₂.Heights
