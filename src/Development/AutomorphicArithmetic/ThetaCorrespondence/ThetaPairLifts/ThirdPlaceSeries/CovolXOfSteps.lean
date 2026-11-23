module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology
namespace GlobalTheory.CovTop.Assembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covolX_of_lift_bounds_and_coreLe : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive → _root_.GlobalTheory.CovTop.LiftTruncation → _root_.GlobalTheory.CovTop.LiftBadSet → _root_.GlobalTheory.CovTop.LiftLambdaBound → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoreBound' → _root_.GlobalTheory.CovTop.LiftLowBound → _root_.GlobalTheory.CovTop.CovolumeBoundOfX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2 (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤ mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith
end GlobalTheory.CovTop.Assembly
end
end
