module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryQuotientIntegralProdOverPlaces
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.unitaryQuotientIntegral_prod_over_places : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  first | exact @GlobalTheory.RealQuotProd.quot_integral_prod | exact GlobalTheory.RealQuotProd.quot_integral_prod | (intros; apply GlobalTheory.RealQuotProd.quot_integral_prod <;> assumption)
