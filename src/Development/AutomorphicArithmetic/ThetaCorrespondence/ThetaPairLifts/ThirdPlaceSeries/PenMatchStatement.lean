module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenXiIsLocFac
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenMatch
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_line_family_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n) (hj : (a.G n).s + 1 ≤ B.R.m),
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    ∀ (α : J.Ch (a.G n).s) (γ : J.Ch ((a.G n).s + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z,
      B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 (a.G n).s (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P) (GlobalTheory.QTw.homOf I l Z (a.G n).s hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))) = c * _root_.GlobalTheory.Fam.PenLoc.penXi_alt a n z := by
  first | exact @_root_.GlobalTheory.Fam.PenLoc.pen_match_alt | exact _root_.GlobalTheory.Fam.PenLoc.pen_match_alt | (intros; apply _root_.GlobalTheory.Fam.PenLoc.pen_match_alt <;> assumption)
end
