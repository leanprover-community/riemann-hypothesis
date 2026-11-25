module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
structure ParityConditions (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (Rw : RowSide D) : Type 1 where
  T : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : LabTrue D T
  chr : CharSide D cf
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T
  A : _root_.GlobalTheory.HeightCounting.AUSideAlt D
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A
  row : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR
def ParityConditions.ofSt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (a : _root_.GlobalTheory.HeightCounting.HeightCountingBaseData hL D cf rep) : _root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D cf rep a.A.row := ⟨a.A.wdT, a.A.lab, a.A.chr, a.cg, a.A.au, a.au, a.row⟩
structure ParityLaws (D : D7) : Prop where
  tie0 : SumRepresentations.tie0 D
  an : SumRepresentations.adm5 D
  temp : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D
  lab : SumRepresentations.tieLab D
  one : GlobalTheory.RowCopy.HeckeSplitOne D
  cancel : ∀ w (a b c : D.naut.LP w), D.naut.lpSum a c = D.naut.lpSum b c → a = b
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)
end GlobalTheory.HeightCounting.Up
end
end
