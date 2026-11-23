module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
noncomputable section
namespace Formalism.MainNotions.Ext.Lw
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.Forms Formalism.BasicNotions
open scoped TensorProduct
theorem rankTiesF_of_C2S_alt {eps : ℝ} (Fm : FamP eps) (h : _root_.Formalism.L2.SecondChernLinkedClass Fm) : RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (Fm.x1 + 1), fun x hx i u => ?_⟩
  have e1 : Fm.x1 < x := by
    have := (le_max_right x0 (Fm.x1 + 1)).trans hx
    linarith
  obtain ⟨T⟩ := h x e1 ((le_max_left _ _).trans hx) i
  exact mu0Tie_of_sym T.cols u
theorem second_chern_linked_closed_rank_ties : Closed _root_.Formalism.L2.SecondChernLinkedClass fun Fm _ => RankTiesF Fm :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hC _ => _root_.Formalism.MainNotions.Ext.Lw.rankTiesF_of_C2S_alt Fm hC⟩⟩
end Formalism.MainNotions.Ext.Lw
end
end
