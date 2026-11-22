module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalEigenData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeVISupIndep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerMapRep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedLocTiedOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingOfRowLiftFamilyMovedDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisationsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedReadingsRelatedLocalizedAdelicDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricCharacterGridListKeptLocalizedStageStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (l : LC hL x)

variable {big : (Dof x).what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 (Dof x))} (Sp : NdSpec l.a.A.pl l.mt.M l.c.ch big L.X L.T)
  (Au : AutSpec l.a.A l.mt.M l.c.tp.tup Sp.iq L.Y L.C) (ss : ∀ σ lam, IsSSRep (L.Z.rbar σ lam))

theorem low_ok (D : D7) : 2 ∈ lowAll D ∧ AbsolutelyIrreducibleSpan.q0 D ∈ lowAll D ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ lowAll D ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := by
  refine ⟨by simp [lowAll, Formalism.L2.lowPr], by simp [lowAll, Formalism.L2.lowPr], fun p hp => ?_, fun p hp => ?_⟩ <;>
    simp only [lowAll, Formalism.L2.lowPr, Finset.mem_union, Finset.mem_insert] <;> tauto

variable (al : AllL l L) (hLg : GlobalTheory.CoefDuty.Large (withLoc L))

-- Transport the character data and the record together so their indices stay aligned.

variable {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y)

def frameY : Formalism.L2.RowFrame (DL x L) := Formalism.L2.Col.rowFrameOf (DL x L) _ Y.eFT

def RowsAt (P : Pre2 K w) : Prop := ∀ x : St P, (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) →
  ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW

end GlobalTheory.HeightCounting.Fin3

end
