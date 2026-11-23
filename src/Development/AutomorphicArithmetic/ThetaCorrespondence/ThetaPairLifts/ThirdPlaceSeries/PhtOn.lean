module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideAAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.phtOn_alt {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {fr : Formalism.L2.OmFrame D} (x : PhtOn A.wd fr fun _ _ _ _ => True) : PhtOn (m.sideA_alt A).wd (m.omFrame fr) fun _ _ _ _ => True := @_root_.GlobalTheory.HeightCounting.PhtOn.mk (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (x.card :)))
end
end GlobalTheory.LayerMove
end
end
