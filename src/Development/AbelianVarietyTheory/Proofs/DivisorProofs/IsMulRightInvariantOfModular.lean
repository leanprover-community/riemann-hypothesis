module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

noncomputable section

open GlobalTheory.WeilM MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

theorem isMulRightInvariant_of_modular {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, modularCharacterFun g = 1) : μ.IsMulRightInvariant :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

end GlobalTheory.ParAvg
