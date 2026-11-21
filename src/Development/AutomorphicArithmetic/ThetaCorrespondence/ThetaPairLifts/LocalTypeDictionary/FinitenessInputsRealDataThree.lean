import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealData
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataThreeStatement

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
namespace GlobalTheory.LowRowAdel
theorem adelC_of_siegelWeil_of_doubling_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  intro hCusp hWS _hSWc hDbl hUnr hBZ hFD D G _ _ Pl0 T A Ks _ _ _ R F hL hStd
  have hHM : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule :=
    GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hLoc : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock := GlobalTheory.SingleBlock.localIntegralSingleBlock
  have hPM : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.T.adelicLift_scalar_of_innerProductFormula R F (GlobalTheory.T.adelicLift_mem_cuspForm_multiplicitySpace hCusp R F) (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law hLoc R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS (_root_.ResidueKilled.sec_of_dm hDbl) R F hL)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM) (deltaNorm_all D)
    (GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL R F (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUnr R F)) (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula hLoc R F hPM)
    (GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames D hStd) (GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra hFD R F)
end GlobalTheory.LowRowAdel
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  first | exact @_root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt | exact _root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt | (intros; apply _root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow
theorem lamLow_closing_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCusp hWS hSWC hDM hUD hBZ hFD D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH
    hOk hSep hChar hEx hPrim hPhs hStd fw hBar hIo hPins hOne hTie hSizes hLow hNum hPar hStdV
  have hAd : AdelC R.toRealDat F.lv2 :=
    _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV hCusp hWS hSWC hDM hUD hBZ hFD R.toRealDat F.lv2 hPar hStdV
  have hCore := (GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hSep hChar hEx hPrim hPhs).1
  have hPT : PrimeToHost R.toRealDat A3.A.μ0 :=
    GlobalTheory.T.badPlacesPrimeToHost_baseTuple R.toRealDat F.lv2 (GlobalTheory.Core5.of_core hCore)
  exact GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation T R F κ v₀ O s b C CH hOk hSep hChar hEx hPrim hPhs hStd fw hBar
    hIo hPins hOne hTie hSizes hLow hNum hAd hPT
end GlobalTheory.LowRow
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @_root_.GlobalTheory.LowRow.lamLow_closing_alt | exact _root_.GlobalTheory.LowRow.lamLow_closing_alt | (intros; apply _root_.GlobalTheory.LowRow.lamLow_closing_alt <;> assumption)
end
end
