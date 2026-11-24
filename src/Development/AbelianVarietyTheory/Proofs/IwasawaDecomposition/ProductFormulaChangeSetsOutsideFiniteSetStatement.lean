module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaChangeSetsOutsideFiniteSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.product_formula_change_sets_outside_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  first | exact @GlobalTheory.GaugeSetChange.product_formula_change_sets | exact GlobalTheory.GaugeSetChange.product_formula_change_sets | (intros; apply GlobalTheory.GaugeSetChange.product_formula_change_sets <;> assumption)
