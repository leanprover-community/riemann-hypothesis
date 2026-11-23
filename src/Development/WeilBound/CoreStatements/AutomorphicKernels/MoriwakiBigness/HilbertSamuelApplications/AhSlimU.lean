module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateOfFarguesExact
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SemiAbelianHomExtension
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.DeepStROfUse
public import Development.WeilBound.CoreStatements.HodgeTatePoints.AhSlim
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace PositivityTheory.HtPt.Ah

open GlobalTheory.CompanionTheory.Ar

theorem deep_slim_use (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) (hU : PositivityTheory.MbHsUse.HSUse)
    (hBig : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement) (hF : HT.FarguesExact) (hZ : GR.ZarhinStatement)
    (hN : Pub.NefRR) : Plug.DeepStR :=
  Plug.deepStR_of_use (ais h₁ h₂ hPL) hU hBig (resK h₁ h₂) GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension
    (GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact hF) GlobalTheory.CompanionTheory.Gaga.gagaSections quot hZ hN

end PositivityTheory.HtPt.Ah
