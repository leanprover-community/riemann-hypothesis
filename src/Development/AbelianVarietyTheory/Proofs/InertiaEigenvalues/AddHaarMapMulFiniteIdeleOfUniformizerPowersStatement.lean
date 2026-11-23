module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  first | exact @GlobalTheory.AdeleScale.map_mul_finId_adl | exact GlobalTheory.AdeleScale.map_mul_finId_adl | (intros; apply GlobalTheory.AdeleScale.map_mul_finId_adl <;> assumption)
