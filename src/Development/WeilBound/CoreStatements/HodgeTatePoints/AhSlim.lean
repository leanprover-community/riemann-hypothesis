module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PoincareLelongOfInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

theorem resK (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero) :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide.resK_of_resolution_principalisation h₁ h₂

theorem ais (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement :=
  Pub.arithIntersectionSystem_of_poincareLelong_resK (Tw.Main.poincareLelong_of_inv (resK h₁ h₂) hPL) (resK h₁ h₂)

theorem quot : GR.QuotientByFiniteFlatStatement :=
  GR.QuotSide.quotientByFiniteFlat_of_freeQuotient GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme_holds

end PositivityTheory.HtPt.Ah
