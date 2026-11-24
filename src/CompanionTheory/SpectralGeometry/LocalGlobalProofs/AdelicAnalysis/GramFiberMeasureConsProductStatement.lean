module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProduct
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

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (u : Rˣ) (w : (Fin n → R ⊗[F] E) → HermR R σ n), Measurable w → ∀ f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞, Measurable f → ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate <;> assumption)
