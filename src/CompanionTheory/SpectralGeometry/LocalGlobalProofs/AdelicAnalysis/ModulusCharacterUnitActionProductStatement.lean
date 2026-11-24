module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProduct
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.modulus_character_unit_action_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F)), μW.IsAddHaarMeasure → μA.IsAddHaarMeasure → ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧ (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1, Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ x : ℝ, (χ (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * x)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | exact GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi | (intros; apply GlobalTheory.CompanionTheory.SW.FChi.exists_modulus_chi <;> assumption)
