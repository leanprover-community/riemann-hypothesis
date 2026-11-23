module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareSizeBoundsAlongFamilyStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhitStatement
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
set_option autoImplicit false
noncomputable section
open Module
namespace GlobalTheory.ShareOn.Alg
end GlobalTheory.ShareOn.Alg
namespace GlobalTheory.ShareOn.Alg
end GlobalTheory.ShareOn.Alg
namespace GlobalTheory.ShareOn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ShareOn
namespace GlobalTheory.ShareOn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
end GlobalTheory.ShareOn
namespace GlobalTheory.ShareOn
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies Formalism.MainNotions.ArithmeticCylinders
theorem shareWSt_of_modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement → _root_.GlobalTheory.ShareOn.SharedWeightStatement := by
  intro hM
  unfold _root_.GlobalTheory.ShareOn.ModelStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt at hM
  unfold _root_.GlobalTheory.ShareOn.SharedWeightStatement _root_.GlobalTheory.BigOn.ForallTwoRuns _root_.GlobalTheory.BigOn.AtPtsAlt
  refine (hM.and GlobalTheory.T.shareSize_bounds_along_family).imp ?_
  intro eps Fm CH _ h
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  refine ⟨max x1 x2, fun x hx hle ι p hp hmore r hr hown i => ?_⟩
  have hm := h1 x hx ((le_max_left _ _).trans hle) ι p hp hmore r hr hown i
  have hn := h2 x hx ((le_max_right _ _).trans hle) ι
  exact shareW_of_modelAt p i _ _ (by positivity) hm (by obtain ⟨_, _, -, -, h⟩ := _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip _ _ _ _ _ _ _ _ _ _ p hp; exact h)
    (fun p0 h0 => (hn p0 h0).1) (hn 0 (Nat.zero_le _)).2
end GlobalTheory.ShareOn
end
end
