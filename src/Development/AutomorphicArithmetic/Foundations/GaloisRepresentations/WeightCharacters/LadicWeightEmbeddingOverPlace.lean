module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.WtDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutCrit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNearH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DomOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EllCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EmbProjHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EvLemOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExistsDual
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpDisj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOffHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightAtEmbeddingOverPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NeatLev
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NrmAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.QROf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SepPoly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SqExpH
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SumRep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopUpOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TorFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistBd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.WExpH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace UpperTheory.Gal.Wt

theorem expBasic_holds : ExpBasic := expBasic_of
theorem expDisj_holds : ExpDisj := expDisj_of
theorem evLem_holds : EvLem := evLem_of
theorem pevExp_holds : PevExp := pevExp_of expBasic_holds
theorem dom_holds : Dom := dom_of
theorem sqExp_holds : SqExp := sqExp_h expBasic_holds evLem_holds dom_holds
theorem topUp_holds : TopUp := topUp_of
theorem torFacts_holds : TorFacts := torFacts_of
theorem qR_holds : QR := qR_of
theorem wtBd_holds : WtBd := wtBd_of expBasic_holds expDisj_holds sqExp_holds topUp_holds torFacts_holds
theorem wExp_holds : WExp := wExp_h expBasic_holds sqExp_holds torFacts_holds
theorem rFinEx_holds : RFinEx := rFinEx_of
theorem deltaNear_holds : DeltaNear := deltaNear_h
theorem autCrit_holds : AutCrit := autCrit_of
theorem autMul_holds : AutMul := autMul_of
theorem nrmAut_holds : NrmAut := nrmAut_of autCrit_holds
theorem famOfA_holds : FamOfA := famOfA_of autMul_holds nrmAut_holds rFinEx_holds
theorem sumRep_holds : SumRep := sumRep_of
theorem neatLev_holds : NeatLev := neatLev_of
theorem ellC_holds : EllC := ellC_of
theorem twist_holds : Twist := twist_of autCrit_holds
theorem twistBd_holds : TwistBd := twistBd_of twist_holds
theorem ladic_weight_embedding_over_place : Kap0 := ladic_weight_at_embedding_over_place
theorem kaplFin_holds : KaplFin := kaplFin_of
theorem kapl_holds : Kapl := kapl_of kaplFin_holds
theorem sepPoly_holds : SepPoly := sepPoly_of kapl_holds
theorem nearSub_holds : NearSub := nearSub_of
theorem pieces_holds : Pieces := pieces_of sepPoly_holds nearSub_holds
theorem famOf_holds : FamOf := famOf_of expBasic_holds pevExp_holds sqExp_holds topUp_holds wExp_holds famOfA_holds
theorem famEx_holds : FamEx := famEx_of neatLev_holds ellC_holds twist_holds twistBd_holds ladic_weight_embedding_over_place pieces_holds deltaNear_holds famOf_holds
theorem famProj_holds : FamProj := famProj_of evLem_holds sumRep_holds
theorem famSum_holds : FamSum := famSum_of expBasic_holds evLem_holds torFacts_holds qR_holds wtBd_holds embProj_holds
theorem famWt_holds : FamWt := famWt_of famOff_holds famSum_holds

theorem wtLacEx_holds : UpperTheory.Gal.Int.Cong.WtLacEx := top_of famEx_holds famProj_holds famWt_holds

end UpperTheory.Gal.Wt
