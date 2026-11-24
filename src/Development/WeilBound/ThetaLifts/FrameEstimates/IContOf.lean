module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
public import Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iCont_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hW : DomWeil) (hS : DomSoU) (hF : SoFin) :
    PositivityTheory.ThKF.ICont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine ⟨fun hw Φ hΦ => ?_, fun _ Φ hΦ => ?_⟩
  · obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.1 Φ hΦ
    have hd := hW F E σ B n d X W M χX χW om r s r' s' hp hw
    rw [show M.I om (∑ i, pureA F (f i) (φ i)) = _ from funext (dom_sum hB hp hd f φ hφ hφ).2.2]
    exact continuous_finsetSum _ fun i _ => dom_continuous hB hT hE hp hd (hφ i) (hφ i) (f i)
  · obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
    have hd := dom_of_domSoU hS hp
    rw [show M.I om (∑ i, pureA F (f i) (φ i)) = _ from funext (dom_sum hB hp hd f φ hφ fun i => (hφ i).1).2.2]
    exact continuous_finsetSum _ fun i _ => dom_continuous hB hT hE hp hd (hφ i) (hφ i).1 (f i)

end PositivityTheory.ThKEst

end
