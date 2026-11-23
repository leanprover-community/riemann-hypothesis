module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedPrim
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemGluedIff
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
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open GlobalTheory.GoodPos
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.MiTop.Scale.Glue
open GlobalTheory.FinPl.FrameLat
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.MiTop.Scale.Glue
namespace GlobalTheory.MiTop.Scale
variable {D : D7}
variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}
end GlobalTheory.MiTop.Scale
namespace GlobalTheory.MiTop
open Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links GlobalTheory.MiS GlobalTheory.Core.Mi GlobalTheory.Fam GlobalTheory.MiTop.Scale
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)}
theorem placedPrim_iff_placedP : _root_.GlobalTheory.MiTop.PlacedPrimitiveConditions f B ↔ _root_.GlobalTheory.MiTop.PlacedConditions f B := by
  unfold _root_.GlobalTheory.MiTop.PlacedPrimitiveConditions _root_.GlobalTheory.MiTop.PlacedConditions
  simp only [topPrim_iff]
theorem rank_X_succ_pos (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : 0 < (f.c.X (j + 1)).rank := by
  refine lt_of_lt_of_eq ?_ (Formalism.L2.Forms.rankN D (j + 1) (by omega)).symm
  unfold Ranks.N
  positivity
end GlobalTheory.MiTop
end
end
