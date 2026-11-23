module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffOfJet
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProductStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatementStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem germOfFam_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → GermOfFamT := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c inst hstar
  obtain rfl := starSt E H inst hstar
  let := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ v hv q hq
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨τ, hτ, ht, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
    C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  refine ⟨fun σ' => ?_, fun s σ' hE hs g hg => ?_⟩
  · obtain ⟨f, hf⟩ := (GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hu τ hτ F q).2.2 (ht htr) σ'
    exact ⟨f, (hiff F q σ' f).2 hf⟩
  · exact GlobalTheory.IntegralGerm.main hL hL2 hL4 hT T.V ϖ hϖ D' A' G' U' _ _ hu τ hτ F v hv q hq σ' s g hE
      ((hiff F q σ' g).1 hg)
      (n1e T.V ϖ hϖ D' _ (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v q s hs)

end GlobalTheory.PowGerm
