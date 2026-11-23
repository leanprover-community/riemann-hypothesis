module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivialLocal
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MemberRanks
theorem admissible_ranks_at_member_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val _root_.GlobalTheory.Fc.BundleCondition (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)
end GlobalTheory.MemberRanks
end
