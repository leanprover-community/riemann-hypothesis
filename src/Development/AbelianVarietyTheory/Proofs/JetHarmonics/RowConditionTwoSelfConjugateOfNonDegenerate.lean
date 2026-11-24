module

public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateFormalBiextensionSquareStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerateStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlaceStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAtSelf

theorem rowCondition_two_selfConjugate_of_nonDegenerate : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), NDG Y → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc :=
  fun C _ _ V O _ _ dd Y d _ I0 _ p h Hc =>
    GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate C V d _ _ (Y.rawSelf p) (GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)
      (GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d I0 p) (GlobalTheory.T.nonDegenerate_formalBiextension_square C V O dd Y d I0 p h) Hc

end GlobalTheory.RowAtSelf
