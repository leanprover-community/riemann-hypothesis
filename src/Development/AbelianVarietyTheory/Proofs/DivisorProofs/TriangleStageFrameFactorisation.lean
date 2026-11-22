module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GbigTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsTwoTriplesAgreeStatement
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsGeoOfSignatureRankBounds
public import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoConst
public import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoUnit
public import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseMain

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Helpers

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StageGeo

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

end Helpers
