module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CongruenceSubgroupOfFormAutomorphisms
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
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.congruence_subgroup_of_form_automorphisms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite ℤ Λ] (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (I : Ideal (𝓞 E)) (M A : ℕ), 0 < M → 0 < A → ∃ Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ), Γ ≤ autGrp form ∧ Γ.relIndex (autGrp form) ≠ 0 ∧ ∀ γ, γ ∈ Γ ↔ (∀ a b, form (γ a) (γ b) = form a b) ∧ (∀ a ∈ I • (⊤ : Submodule (𝓞 E) Λ), ∃ e, γ a = a + M • e) ∧ ∀ a, ∃ e, γ a = a + A • e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.levelGrp_finite_index | exact GlobalTheory.CompanionTheory.Ar.Cusp.levelGrp_finite_index | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.levelGrp_finite_index <;> assumption)
