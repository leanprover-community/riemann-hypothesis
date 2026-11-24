module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.E.E3

theorem sizet_holds : SizeT := by
  intro E _ _ _ N Q₁ Q₂ h₁ h₂
  obtain ⟨hcpt, -, -, c, hc⟩ :=
    GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E N
  obtain ⟨r₁, hr₁⟩ := hcpt Q₁ h₁
  obtain ⟨r₂, hr₂⟩ := hcpt Q₂ h₂
  have htor := GlobalTheory.CompanionTheory.TorNorm.torNorm GlobalTheory.CompanionTheory.LogAbs.logAbsBasic E
  have hd : (0 : ℝ) ≤ 2 * Module.finrank ℚ E := by positivity
  refine ⟨|r₁| + |r₂| + 2 * |c| + 2 * Module.finrank ℚ E, by positivity, fun q₁ hq₁ q₂ hq₂ x => ?_⟩
  have e₁ := hc (q₁ * An.tor E x) q₂
  have e₂ := hc q₁ (An.tor E x)
  have e₃ := (htor.2 N x).2
  have a₁ := (hr₁ q₁ hq₁).trans (le_abs_self r₁)
  have a₂ := (hr₂ q₂ hq₂).trans (le_abs_self r₂)
  have a₃ := le_abs_self c
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have m₁ : 0 ≤ (|r₁| + |r₂| + 2 * |c|) * ‖x‖ := mul_nonneg (by positivity) hx
  nlinarith

end PositivityTheory.Rg.BcB.E.E3

end
