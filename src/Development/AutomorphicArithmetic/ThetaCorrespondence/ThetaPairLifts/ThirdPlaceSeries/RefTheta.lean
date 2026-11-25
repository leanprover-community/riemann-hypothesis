module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]
end Free
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
def SumPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1
def ReferenceCore : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C
def ReferenceTheta : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C
def ReferenceWeight : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C
end GlobalTheory.RefSum
end
end
