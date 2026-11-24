module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section
noncomputable section
namespace GlobalTheory.NPin
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

structure CharacterChoiceData (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) where
  cf : CharFrame D
  C : NChoice D
  tp : TupTied D cf C
  chr : NCharTied D cf C tp
  val : ValLL0 D cf
  Q_eq : ∀ i, D.nd.Q i = C.Q (D.nd.w i)
  T : WDTie D.nd D.naut
  lab : LabTrue D T
  cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T
  M : MtFam D
  H : _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tp.tup
  au : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T H.au
  rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r
  rep_inj : ∀ σ σ', (rep σ).Iso (rep σ') → σ = σ'
  row : ∀ i, _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (D.naut.locW i σ w)) (D.naut.satW i)
  locW_eq : ∀ i i' σ w, D.naut.locW i σ w = D.naut.locW i' σ w
  jE : D.host.E →+* Qb
  ty : TypesOpen D jE
  wd : WDSide D T
  wdOf : ∀ (i : D.nd.Loc) a (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) w,
    D.naut.wdOf i r w = wd.wdOf (D.nd.l i) (D.naut.iotaQC i) r w ∧
    (D.naut.IsCrysW i r w ↔ wd.IsCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsPotCrysW i r w ↔ wd.IsPotCrysW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    (D.naut.IsdRW i r w ↔ wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w) ∧
    ∀ τ, D.naut.jumpsW i r τ = wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ
def weilDeligneOfLocalIrrep (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n) :
    GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w) :=
  _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls π.toIrrRep)
structure IsFaithfulReading {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T) : Prop where
  rc : ∀ i w hw, (S i w hw).rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w
  row : ∀ i (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w) σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ →
    IsLocS (P.rep σ).S s ((S i s.w hw).row σ).toIrrRep
  rep : ∀ i (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w) Q,
    IsLocS (n := D.R.nV) (P.H.av.S i Q) s ((S i s.w hw).rep Q).toIrrRep
  mu : ∀ i w hw (j : Fin D.R.m), j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) w (S i w hw).mu
  eta : ∀ i w hw, IsComp P.cf.eta w (S i w hw).eta
structure CharacterChoiceJoin {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) : Type 1 where
  form : ∀ i, MtForm D P.M i
  rowM : ∀ i : D.nd.Loc, RowMod D P.rep (D.nd.j i)
  th : ∀ (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i →
    ThetaMod D P.M i (rowM i) (P.tp.tup (D.nd.mu i) j) P.cf.eta
end GlobalTheory.NPin
end
end
