module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeepStROfVolume
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GivenOfUse
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GoodTowerVolumeTheoremBis
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.LineOfLargeDegreeOfUse
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
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin

@[expose] public section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem deepStR_of_use : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement → Pub.NefRR → Plug.DeepStR := by
  intro hAIS hU hMB hResK hSA hFHT hGaga hQ hZ hNef
  have hLLD := GlobalTheory.CompanionTheory.Ar.Giv.lineOfLargeDegree_of_use hAIS hU hMB hResK
  have hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given := GlobalTheory.CompanionTheory.Ar.Link.given_of_use hAIS hU hMB hResK hSA hFHT hGaga hLLD
  have hTC := GlobalTheory.CompanionTheory.Ar.Link.good_tower_volume_theorem_bis hAIS hU hMB hResK hSA hFHT hGaga hLLD hQ hZ
  have hHS : Prov.HS := by
    unfold _root_.GlobalTheory.CompanionTheory.Ar.Top.Given at hG
    exact hG.2.2.2.2.2.2.2.2.2.2.1
  have hG6 : ReciprocityTheory.ChartRestriction.G.Geo.BirationalPullbackPushforwardFormula := by
    unfold Prov.HS at hHS
    exact hHS.2.2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_volume hNef hG hAIS hG6 hTC.1 hTC.2

end GlobalTheory.CompanionTheory.Ar.Plug
