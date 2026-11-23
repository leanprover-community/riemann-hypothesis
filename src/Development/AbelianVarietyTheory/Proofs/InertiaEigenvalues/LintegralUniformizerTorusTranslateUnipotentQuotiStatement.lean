module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUniformizerTorusTranslateUnipotentQuoti
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  first | exact @GlobalTheory.CellDec.lintegral_tl_inv_mul | exact GlobalTheory.CellDec.lintegral_tl_inv_mul | (intros; apply GlobalTheory.CellDec.lintegral_tl_inv_mul <;> assumption)
