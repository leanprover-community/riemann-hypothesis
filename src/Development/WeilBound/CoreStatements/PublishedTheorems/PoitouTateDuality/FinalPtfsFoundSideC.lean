module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSideA
public import Mathlib.RingTheory.PicardGroup
public import ReciprocityTheory.GaloisValuations.Global
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSideB
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion PositivityTheory.LocalTateOrthogonality.Gcoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxSynthPendingDepth 1

section Local

variable {Kf : FiniteSubfield} [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
  {S : Set (HeightOneSpectrum (𝓞 Kf.1))} [Fintype S] {l r : ℕ} [Fact l.Prime]
  {ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)}
  {v : S} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A}

theorem cyc_dec {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (l ^ r)) (g : Dec (F := Kf.1) A) :
    (g : G Kf.1 (AlgebraicClosure ℚ)) ζ = ζ ^ ((cycMod Kf.1 (AlgebraicClosure ℚ) l r
      (g : G Kf.1 (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val :=
  cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
    (MulSemiringAction.toRingAut (G Kf.1 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)
      (g : G Kf.1 (AlgebraicClosure ℚ))) ζ hζ.pow_eq_one



theorem rvF_act
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (l ^ r))
    (u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S))
    (hu : ((((u : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ)
    (σ : AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) (m : ZMod (l ^ r)) :
    rvF S u (((cycMod Kf.1 (AlgebraicClosure ℚ) l r ((ev σ : Dec (F := Kf.1) A) :
        G Kf.1 (AlgebraicClosure ℚ)) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m) =
      (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))).ρ σ (rvF S u m) := by
  have hτ := cyc_dec hζ (ev σ)
  have hζN : ζ ^ (l ^ r) = 1 := hζ.pow_eq_one
  have hmod : ∀ k : ℕ, ζ ^ (k % (l ^ r)) = ζ ^ k := fun k => by
    conv_rhs => rw [← Nat.mod_add_div k (l ^ r), pow_add, pow_mul, hζN, one_pow, mul_one]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  have key : ∀ a : ZMod (l ^ r), ((((Additive.toMul (rvF S u a) : rootsOfUnity (l ^ r)
      (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) = ζ ^ a.val := fun a =>
    (rvF_coe S u a).trans (by rw [hu])
  refine (key _).trans ?_
  refine Eq.trans ?_ (gsFin_apply_eq hev σ _).symm
  refine Eq.trans ?_ (congrArg (fun x => ((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) (key m)).symm
  rw [map_pow, hτ, ← pow_mul, ZMod.val_mul, hmod]

end Local

end PositivityTheory.Lit1.PTN
