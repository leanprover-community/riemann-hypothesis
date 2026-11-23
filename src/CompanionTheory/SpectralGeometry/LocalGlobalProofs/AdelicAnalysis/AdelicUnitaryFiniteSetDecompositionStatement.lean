module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecomposition
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_unitary_finite_set_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureH.pure_h | exact GlobalTheory.CompanionTheory.SW.PureH.pure_h | (intros; apply GlobalTheory.CompanionTheory.SW.PureH.pure_h <;> assumption)
