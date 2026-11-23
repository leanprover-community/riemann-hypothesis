module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtQIffRowQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCodimOneStalkDvr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.AutTHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.BadFinite
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.CsdLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownCrys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownDR
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownPhi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ExistsQuadraticCMExtSplitAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.IsoOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinEndHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneUsHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PhiPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.RamUnr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.FirstQuadraticSquareHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClAway
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDenseId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDgFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatAE
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

namespace UpperTheory.Gal.Int.Core

open UpperTheory.Gal.TP

theorem joinU_holds : JoinU :=
  joinU_of oneUs_holds isoOne_holds phiPol_holds autT_holds Sub.satAE_holds Sub.clConj Sub.satPol_holds Sub.clAway_holds

theorem subtractQ_holds : SubtractQ :=
  subtractQ_of Sub.charEx Sub.satAE_holds (Sub.denseId_holds Sub.cpFacts_holds Sub.dgFacts_holds) Sub.cpFacts_holds Sub.peelAll
    Sub.clTw Sub.contLeft_holds Sub.sSLeft_holds Sub.satPol_holds Sub.clConj

theorem joinAll_holds : JoinAll := joinAll_of oneUs_holds subtractQ_holds

theorem sphDown_holds : ∀ c, SphDown c
  | .unr => downUnr_holds
  | .dR => downDR_holds
  | .crys => downCrys_holds
  | .phi => downPhi_holds

theorem stepDown_holds : StepDown :=
  stepDown_of isoOne_holds (patchOne_holds isoOne_holds oneTower_holds oneConj_holds) sphDown_holds

theorem joinUp_holds : JoinUp :=
  joinUp_of' stepDown_holds csdLift_holds ramUnr_holds oneUs_holds exists_quadratic_CM_ext_split_at

theorem rowCsd_of (hT : TwoUpOK) (hD : GlobalTheory.Cong.DescOffT) (hL : LimU) : RowCsd :=
  joinUp_holds PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity UpperTheory.Gal.AbelianGaloisNormality.gk_holds
    (GlobalTheory.QuadLiftBridge.quadLift UpperTheory.Gal.AbelianGaloisNormality.strongTC_holds PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity)
    (joinGL_holds hD (joinAll_holds hT (joinU_holds hL)))

theorem core_of_limU (hT : TwoUpOK) (hD : GlobalTheory.Cong.DescOffT) (hL : LimU) : GlobalTheory.RoadU.Core :=
  GlobalTheory.RoadW.core_of_rowStarCore (joinEnd_holds (rowCsd_of hT hD hL))

theorem core_of_limOdd (hT : TwoUpOK) (hC : GlobalTheory.CongPhi.ClosedPhi) (hD : GlobalTheory.Cong.DescOffT) (hL : LimOdd) : GlobalTheory.RoadU.Core :=
  core_of_limU hT hD (limU_of_limOdd hC hL)

theorem limOdd_of_limFinOdd (h : GlobalTheory.CongL.LimFinOdd) : LimOdd := fun E Ω _ _ _ _ _ _ l _ ι a ha => h E Ω l ι a ha.pos ha

theorem toCore (hT : TwoUpOK) : GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  fun hC hD hL => core_of_limOdd hT hC hD (limOdd_of_limFinOdd hL)

end UpperTheory.Gal.Int.Core
