module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.NumSizes
variable {D : D7} {L : SizeData₂ D}
variable {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem numPt_alt : _root_.GlobalTheory.RefSum.NumPtAlt := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨|Fm.Ct| + 20, by positivity,
    Real.exp (Real.exp 1), fun x hx hle ι p _ i _ => by
      rw [← Fm.Ct_eq x ι]
      refine numAt p i (Fm.parT x hx ι) ?_
      rw [Fm.L_x x ι hx, Real.le_log_iff_exp_le, Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le hle)]
      · exact hle
      · exact Real.log_pos ((Real.one_lt_exp_iff.2 (Real.exp_pos 1)).trans_le hle)⟩⟩⟩
theorem numPt_of_size' : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := fun _ => _root_.GlobalTheory.RefSum.NumSizes.numPt_alt
end GlobalTheory.RefSum.NumSizes
end
end
