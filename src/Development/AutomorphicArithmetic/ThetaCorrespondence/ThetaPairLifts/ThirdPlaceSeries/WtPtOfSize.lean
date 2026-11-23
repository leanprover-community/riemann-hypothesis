module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZStatement
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



section
set_option autoImplicit false

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.MeanTop
namespace GlobalTheory.RefSum.DivWt
variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (h : W.Hyp) (hd : W.IsDiv)
include h hd
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem wtPt_of_wtN_alt (h : _root_.GlobalTheory.CovTop.LiftWeightNumerator) : _root_.GlobalTheory.RefSum.WtPtAlt :=
  Closed.imp h fun Fm _ _ ⟨_, _, a, h⟩ => ⟨802, by norm_num, a, fun x hx hle ι p hp i hi u1 hq =>
    wtAt_of_wtNum p i (h x hx hle ι p hp i) (le_PP (Fm.parT x hx ι)) hi u1 hq⟩
theorem wt_pt_of_cov_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.WtPtAlt := fun _ => _root_.GlobalTheory.RefSum.DivWt.wtPt_of_wtN_alt _root_.GlobalTheory.T.lift_weight_numerator
end GlobalTheory.RefSum.DivWt
end
end
