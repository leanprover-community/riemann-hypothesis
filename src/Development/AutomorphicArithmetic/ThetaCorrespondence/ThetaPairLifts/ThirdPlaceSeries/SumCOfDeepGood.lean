module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlopeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions
namespace GlobalTheory.CovTop
theorem sumC_of_deepGood_alt : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩
end GlobalTheory.CovTop
end
