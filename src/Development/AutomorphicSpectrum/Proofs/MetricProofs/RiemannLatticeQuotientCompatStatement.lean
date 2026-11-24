module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeQuotientCompat
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

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.riemannLattice_quotient_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R₁ : RiemLat E g' Λ') (D : AddSubgroup Λ) (π : Λ → Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm' : Matrix (Fin g') (Fin g') ℂ) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ)), (∀ x', ∃ x ∈ D, π x = x') → (∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y) → (∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x) → (∀ x ∈ D, π x = 0 → q (R.P x) = 0) → (∀ a z, B' a (q z) = q (R.B a z)) → Hm'.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) → (∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₁.form (π x) (π y)) → ∃ R' : RiemLat E g' Λ', R'.form = R₁.form ∧ R'.Hm = Hm' ∧ ∀ x ∈ D, R'.P (π x) = q (R.P x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot | exact GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_assemble_of_quot <;> assumption)
