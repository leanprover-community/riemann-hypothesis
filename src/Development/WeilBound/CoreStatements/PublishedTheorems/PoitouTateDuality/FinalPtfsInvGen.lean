module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import Mathlib.RingTheory.PicardGroup
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsChi
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSide
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsKummer
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsUnif
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem invMatch_gen' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : InvNormalised ζ inv)
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
     :
    ∃ (z0 : Z2 (muLoc Kf.1 l r A)) (x0 : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2), (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)), ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x0) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ (z0.1 (ev (s 0), ev (s 1))).val) ∧
      inv A (Submodule.Quotient.mk z0) = 1 ∧
      gsLocalInvRootsQZ S ιs (l ^ r) v (cohomologyπ _ 2 x0) = - zmodToQZ (l ^ r) 1 := by
  have hN0 : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hU := exists_uniformizer_ord' (↥Kf.1) (v : HeightOneSpectrum (𝓞 Kf.1))
  obtain ⟨ϖ, hϖv, hϖ2, hord⟩ := hU
  have hϖ0 : (ϖ : ↥Kf.1) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ϖ = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [h']
    exact Submodule.zero_mem _
  have hy0 : ∃ y : AlgebraicClosure ℚ,
      y ^ (l ^ r) = algebraMap (↥Kf.1) (AlgebraicClosure ℚ) (ϖ : ↥Kf.1) :=
    IsAlgClosed.exists_pow_nat_eq _ hN0
  obtain ⟨y, hy⟩ := hy0
  have hK := exists_kummer' (↥Kf.1) A ζ hζ (ϖ : ↥Kf.1) hϖ0 y hy
  obtain ⟨κ, hκ, hκc, hκcoc⟩ := hK
  have hC := exists_chi' Kf (v : HeightOneSpectrum (𝓞 Kf.1)) A hA ⟨l ^ r, hN0⟩ (ιs v) ev hev
  obtain ⟨χ, hχadd, hχIne, hχFrob, hχc, hχev⟩ : ∃ χ : Dec (F := Kf.1) A → ZMod (l ^ r),
      (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) ∈ Ine (F := Kf.1) A → χ g = 0) ∧
      (∀ g : Dec (F := Kf.1) A,
        IsFrob (F := Kf.1) A (normV (v : HeightOneSpectrum (𝓞 Kf.1))) (g : G Kf.1 (AlgebraicClosure ℚ)) →
        χ g = 1) ∧
      Continuous χ ∧
      ∀ σ, χ (ev σ) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ⟨l ^ r, hN0⟩ σ := hC
  have hF := found_side' Kf S hr hS ζ hζ ιs v A hA ev hev ϖ hord y hy κ hκ χ hχev
  obtain ⟨x0, hx0, hinv0⟩ := hF
  have hcont : Continuous (fun p : Dec (F := Kf.1) A × Dec (F := Kf.1) A => κ p.1 * χ p.2) :=
    (continuous_of_discreteTopology (f := fun q : ZMod (l ^ r) × ZMod (l ^ r) => q.1 * q.2)).comp
      ((hκc.comp continuous_fst).prodMk (hχc.comp continuous_snd))
  let z0 : Z2 (muLoc Kf.1 l r A) := ⟨fun p => κ p.1 * χ p.2, hcont, fun g h k => by
    show ((cycMod Kf.1 (AlgebraicClosure ℚ) l r (g : G Kf.1 (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) :
        ZMod (l ^ r)) * (κ h * χ k) - κ (g * h) * χ k + κ g * χ (h * k) - κ g * χ h = 0
    rw [hκcoc, hχadd]
    ring⟩
  refine ⟨z0, x0, hx0, ?_, hinv0⟩
  exact (hinv A v.1 hA).2 ϖ y κ χ z0 hϖv hϖ2 hy hκ hχadd hχIne hχFrob (fun g h => rfl)

end PositivityTheory.Lit1.PTN
