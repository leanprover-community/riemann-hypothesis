module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.NormScaleHaar
open Formalism.UG GlobalTheory.AdelicU

theorem ideleModule_norm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule F (Units.map (Algebra.norm (AF F)) t) : ℝ)) = (absE F E t : ℝ) := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  have h := NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv t)
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Eq.trans ?_ h.symm)
  · rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow, coe_nnnorm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

end GlobalTheory.NormScaleHaar
