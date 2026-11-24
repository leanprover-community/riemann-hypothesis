module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.levelTestFunction_finite_sum_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, IsSB (D.phi bas hn v₀ L Λ) ∧ IsVac X bas D.w (tens Λ (D.sh L)) (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ (∀ L' ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), s.card = Nat.card D.J ∧ (∀ y ∈ s, y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • (L ⊓ L')) ∧ ‖D.dat hn y‖ = 1 ∧ ∀ y' ∈ s, (∀ k, Cong X D.𝔪 (y k) (y' k)) → y = y') ∧ D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ D.phi bas hn v₀ L' Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')))) ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ t : ℂ, ‖t‖ = 1 → wG X bas idx γ (v₀ L) = t • v₀ (mapL γ L) → wG X bas idx γ (D.phi bas hn v₀ L Λ) = (t * ((D.lam k : ℂˣ) : ℂ)⁻¹) • D.phi bas hn v₀ (mapL γ L) Λ := by
  first | exact @GlobalTheory.SW.RecSum.phi_sum_equivariant | exact GlobalTheory.SW.RecSum.phi_sum_equivariant | (intros; apply GlobalTheory.SW.RecSum.phi_sum_equivariant <;> assumption)
