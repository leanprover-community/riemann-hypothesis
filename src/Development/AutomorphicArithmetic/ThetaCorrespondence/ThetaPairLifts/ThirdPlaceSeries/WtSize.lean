module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumLeAtIndex
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoversOfLifts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

@[expose] public section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
open GlobalTheory.FlagTan (dimFlag)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
variable (P : WtPar Dw)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.WtRun
namespace GlobalTheory.CovTop.WtRun
theorem wt_size_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ j ≤ lenT p i PP, ∑ τ, ∑ k, |((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt j τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * kap p i := by
  intro hS
  have hL : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => SizeAt p i PP C ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 0) ∧ WtNum p i PP := by
    refine (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) _root_.GlobalTheory.CovTop.WtShape.wtN_z)).imp
      fun Fm CH _ hh => ?_
    obtain ⟨⟨C, hC, a, ha⟩, ⟨C', -, b, hb⟩, ⟨C'', -, c, hc⟩⟩ := hh
    exact ⟨C, hC, max a (max b c), fun x hx hle ι p hp i =>
      ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i,
       ⟨C', hb x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
       hc x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt hL fun Fm x hx ι p i C _ h _ Y _ => by
    obtain ⟨h1, ⟨A, h2⟩, h3⟩ := h
    exact fun j hj => sum_abs_wt_le_point p i h1 h2 h3 hj
end GlobalTheory.CovTop.WtRun
end
