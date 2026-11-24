module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedProductMeasureCountable
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_restricted_product_measure_countable : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  first | exact @GlobalTheory.GaugeEx.AbsProd.exists_restricted_product | exact GlobalTheory.GaugeEx.AbsProd.exists_restricted_product | (intros; apply GlobalTheory.GaugeEx.AbsProd.exists_restricted_product <;> assumption)
