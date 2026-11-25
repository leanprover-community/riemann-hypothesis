module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def SideCond (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal ∧ PsiUnramAt ψ v ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → w.valuation D.host.E D.host.xi0 = 1

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}


end Cusp

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
