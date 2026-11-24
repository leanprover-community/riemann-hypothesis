module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NotMemQBase
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
noncomputable section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
def qPrime_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) (p : ℕ) : Prop := ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal
def FamilyRatioCondition {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) : Prop :=
  ∀ n, 2 * n = D.R.m → ∀ t, (f.t t).cTop n ≠ 0 ∧ UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W t) ((f.t t).cTop n / (f.t t).cBot)
    ((f.t W.P.A3.A.μ0).cTop n / (f.t W.P.A3.A.μ0).cBot)
def FamilyServedCondition (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∀ w (p : ℕ), p.Prime → _root_.GlobalTheory.MiTop.qPrime_alt W (W.Q.Rl.mu w) p → (p : 𝓞 D.what₂.LL) ∉ w.asIdeal
def FamilyAllConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop :=
  ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (d : _root_.GlobalTheory.MiTop.BottomData W u),
    d.Pin z ∧ LawsX f.t ∧ _root_.GlobalTheory.MiTop.LinkVanishes f d ∧ _root_.GlobalTheory.MiTop.LinkTailCondition f ∧ _root_.GlobalTheory.MiTop.LinkDescends f ∧ _root_.GlobalTheory.MiTop.LinkSurjective f ∧ _root_.GlobalTheory.MiTop.LinkCommutes f ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition f
end GlobalTheory.MiTop
end
end
