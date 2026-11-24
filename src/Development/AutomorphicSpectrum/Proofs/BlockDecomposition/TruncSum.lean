module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Mass.MeanV

variable {F : Type} [Field F] [NumberField F]

def IntOut (T : Finset (HeightOneSpectrum (𝓞 F))) : Set F :=
  {x | ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F}

def GoodFac (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ) : Prop :=
  ContinuousOn g {0}ᶜ ∧ (∀ s, s ∉ v.adicCompletionIntegers F → g s = 0) ∧
    (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
    (∀ s : Fv F v, Valued.v s = 1 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ∧ ∫ s, g s ∂lam = 1

def truncSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
    (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1

def fullSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0},
    G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
