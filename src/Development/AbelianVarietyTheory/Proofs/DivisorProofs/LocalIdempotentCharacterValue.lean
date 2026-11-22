module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  have h1 : ∀ z : AF F, At (evFin F v) z → GlobalTheory.LatVac.liftV v 1 * z = z := by
    intro z hz
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul] at this
    linear_combination -this
  have h2 := GlobalTheory.LatVac.at_liftV v 1 (b - GlobalTheory.LatVac.liftV v (evFin F v b))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h2
  have h3 := h1 _ (GlobalTheory.LatVac.at_liftV v (evFin F v b))
  linear_combination h2 + h3

omit [NumberField E] in
theorem smul_eq_map (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl (F := F)} {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])

end GlobalTheory.SwapAtPlace
