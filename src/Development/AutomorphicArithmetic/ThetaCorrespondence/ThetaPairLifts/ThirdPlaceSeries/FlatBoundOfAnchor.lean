module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatAtOfSplitCovering
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatValStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
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
section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw
namespace GlobalTheory.FlatSplit
section Congr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}
end Congr
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)
end Weights
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.FlatSplit
namespace GlobalTheory.FlatSplit
theorem flat_alt_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.FlatnessCondition := by
  intro hP hDG hFD hA
  refine Closed.imp (Closed.and (Closed.and (Closed.and (Closed.and hDG (_root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD)) hA) _root_.GlobalTheory.T.lift_weight_numerator)
    (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨CA, hCA, h3⟩⟩, ⟨C4, -, h4⟩⟩, ⟨C5, -, h5⟩⟩
  refine ⟨11 * CA + 83, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := (((h1.and h2).and h3).and h4).and h5
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hx x hx' hle ι p hp
  exact _root_.GlobalTheory.FlatSplit.flat_at_of_split_covering p i Y hY hP (a1 i hi Y hY) (a2 i hi Y hY) (a3 i) (a4 i) (a5 i)
end GlobalTheory.FlatSplit
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.flat_of_prints_deepGood_flatDeg_anchor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.FlatnessCondition := by
  exact @_root_.GlobalTheory.FlatSplit.flat_alt_alt
end
end
