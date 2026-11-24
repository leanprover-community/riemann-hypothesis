module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplitHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.QuotObjLink
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PGrpFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PIdealInd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPlaceOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPtAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.CovMain

open UpperTheory.Gal.FiniteEtaleModels in
theorem mIn : MIn :=
  { ex := @GlobalTheory.T.harrisTaylorIntegralModel_nonempty,
    proj := @GlobalTheory.UPel.HT.Model.isProjOver_of_compactB,
    cmp := @GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre,
    finModel := finModel_holds (finCover_holds
      (repAll_holds idealInd_holds (repMul_holds crtMul_holds crtProj_holds))
      (ptAll_holds idealInd_holds crtMul_holds) grpFin_holds),
    placeOf := placeOf_holds,
    cong := crystallineComparison.Mod.congKS_link,
    corr := crystallineComparison.Mod.corrBC_holds crystallineComparison.Mod.quotObj_link }

theorem ksCong_holds : KSCong := kSCong_of mIn
theorem stdEx_holds : StdEx := stdEx_of mIn
theorem ksCover_holds : KSCover := kSCover_of mIn

end UpperTheory.Gal.Int.Geo.CovMain
