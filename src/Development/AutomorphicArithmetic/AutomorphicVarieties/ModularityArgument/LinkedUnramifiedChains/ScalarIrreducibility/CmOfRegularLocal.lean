module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDSerre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRegularElement
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

open GroundTheory.Heights₂.Heights in
private theorem cm_of_regular_local (A : Type) [CommRing A] [IsRegularLocalRing A] :
    IsCohenMacaulayLocalRing A := by
  haveI hL : IsLocalRing A := IsRegularLocalRing.toIsLocalRing
  haveI hN : IsNoetherian A A := IsRegularLocalRing.toIsNoetherian
  obtain ⟨rs, hreg, hmax, hlen⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := A)
  refine @IsCohenMacaulayLocalRing.mk A _ hL hN ⟨rs, fun r hr => ?_, hreg.toIsWeaklyRegular, hlen.symm⟩
  rw [← hmax]
  exact Ideal.subset_span hr


open GroundTheory.Heights₂.Heights in
private theorem ass_min_of_surj {A B : Type} [CommRing A] [IsCohenMacaulayLocalRing A] [CommRing B]
    [Nontrivial B] (φ : A →+* B) (hφ : Function.Surjective φ) {k : ℕ} (x : Fin k → A)
    (hx : ∀ i, x i ∈ maximalIdeal A) (hk : RingHom.ker φ = Ideal.span (Set.range x))
    (hd : ringKrullDim B + (k : WithBot ℕ∞) ≤ ringKrullDim A) {P : Ideal B}
    (hP : P ∈ associatedPrimes B B) : P ∈ minimalPrimes B := by
  classical
  set I : Ideal A := Ideal.span (Set.range x) with hI
  let e : A ⧸ I ≃+* B := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have hdimB : ringKrullDim B = ringKrullDim (A ⧸ I) := (ringKrullDim_eq_of_ringEquiv e).symm
  have hs : ((Finset.univ.image x : Finset A) : Set A) = Set.range x := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcard : (Finset.univ.image x).card ≤ k :=
    Finset.card_image_le.trans (Finset.card_fin k).le
  have hle : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) := by
    have h0 := ringKrullDim_le_ringKrullDim_quotient_add_card (R := A) (Finset.univ.image x) (by
      rw [hs, IsLocalRing.ringJacobson_eq_maximalIdeal]
      rintro _ ⟨i, rfl⟩
      exact hx i)
    rw [hs] at h0
    refine h0.trans ?_
    gcongr
  have heq : ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) = ringKrullDim A :=
    le_antisymm (hdimB ▸ hd) hle
  have hCM : IsCohenMacaulayLocalRing (A ⧸ I) :=
    CMParameterQuotient.proof CMRegularElement.proof A k x hx heq
  have : IsCohenMacaulayLocalRing B := IsCohenMacaulayLocalRing.of_ringEquiv e
  exact mem_minimalPrimes_of_mem_associatedPrimes hP

private theorem min_of_localized {R : Type} [CommRing R] (Q : Ideal R) [Q.IsPrime] {P : Ideal R}
    (hP : P ∈ associatedPrimes R R) (hPQ : P ≤ Q)
    (h : ∀ P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q),
      P' ∈ minimalPrimes (Localization.AtPrime Q)) : P ∈ minimalPrimes R := by
  have hPprime : P.IsPrime := hP.1
  have hdis : Disjoint (Q.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    intro a ha haP
    exact ha (hPQ haP)
  set P' : Ideal (Localization.AtPrime Q) := P.map (algebraMap R (Localization.AtPrime Q)) with hP'
  have hcomap : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hPprime hdis
  have hass : P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q) := by
    refine Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      Q.primeCompl (Algebra.linearMap R (Localization.AtPrime Q)) P' ?_
    rw [hcomap]
    exact hP
  have hmin : P' ∈ (Ideal.map (algebraMap R (Localization.AtPrime Q)) (⊥ : Ideal R)).minimalPrimes := by
    rw [Ideal.map_bot]
    exact h P' hass
  rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q) (⊥ : Ideal R)] at hmin
  have key : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' ∈ (⊥ : Ideal R).minimalPrimes := hmin
  rw [hcomap] at key
  exact key

theorem UpperTheory.V.J.unmix :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (N N' : ℕ) (R : Type) [CommRing R]
        (p : MvPowerSeries (Fin N) O →+* R) (f : Fin N' → MvPowerSeries (Fin N) O), Function.Surjective p → RingHom.ker p = Ideal.span (Set.range f) →
        ∀ Q : Ideal R, Q.IsPrime → Q.height + N' ≤ (Q.comap p).height → ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R := by
  intro O _ _ _ _ N N' R _ p f hp hker Q hQ hht P hP hPQ
  set q : Ideal (MvPowerSeries (Fin N) O) := Q.comap p with hq
  haveI : IsRegularLocalRing (MvPowerSeries (Fin N) O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin N)
  haveI : IsRegularLocalRing (Localization.AtPrime q) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime q
  haveI : GroundTheory.Heights₂.Heights.IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
    cm_of_regular_local _
  let φ : Localization.AtPrime q →+* Localization.AtPrime Q := Localization.localRingHom q Q p rfl
  have hφ : Function.Surjective φ := RingHom.surjective_localRingHom_of_surjective p hp Q
  have hkerφ : RingHom.ker φ = (RingHom.ker p).map (algebraMap _ (Localization.AtPrime q)) :=
    IsLocalization.ker_map (M := q.primeCompl) (S := Localization.AtPrime q)
      (Localization.AtPrime Q) p (Submonoid.map_comap_eq_of_surjective hp Q.primeCompl)
  have hkx : RingHom.ker φ = Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (f i))) := by
    rw [hkerφ, hker, Ideal.map_span, ← Set.range_comp]
    rfl
  have hx : ∀ i, algebraMap _ (Localization.AtPrime q) (f i) ∈ maximalIdeal (Localization.AtPrime q) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
    have hfi : f i ∈ RingHom.ker p := by
      rw [hker]
      exact Ideal.subset_span ⟨i, rfl⟩
    show p (f i) ∈ Q
    rw [RingHom.mem_ker.mp hfi]
    exact Q.zero_mem
  have hd : ringKrullDim (Localization.AtPrime Q) + (N' : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
    exact_mod_cast hht
  refine min_of_localized Q hP hPQ ?_
  intro P' hP'
  exact ass_min_of_surj φ hφ _ hx hkx hd hP'
