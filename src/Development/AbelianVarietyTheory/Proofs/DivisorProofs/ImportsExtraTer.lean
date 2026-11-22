module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.PublishedTheorems.ThetaCharacteristics.ThetaCharZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot

@[expose] public section

namespace GlobalTheory.LiftAndFactorization

open Formalism.L2.Pj

theorem exists_lift (T : CDVR) (x : T.Fr) (hx : x ≠ 0 → vV T.V x = 0) :
    ∃ b : T.V, algebraMap T.V T.Fr b = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 h0
  have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0 := by
    have := hx h0
    unfold vV valV at this
    exact neg_eq_zero.1 this
  have := WithZero.exp_log hne
  rw [hlog, WithZero.exp_zero] at this
  exact this.ge

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr)
    (h : ∀ a : F, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  have key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a := fun a =>
    exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))
  choose f hf using key
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => inj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, ?_⟩
  ext a
  exact hf a

end GlobalTheory.LiftAndFactorization
