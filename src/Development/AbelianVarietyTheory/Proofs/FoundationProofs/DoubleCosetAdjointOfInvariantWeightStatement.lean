module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetAdjointOfInvariantWeight
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.double_coset_adjoint_of_invariant_weight : ∀ (G X Γ ι κ : Type) [Group G] [MeasurableSpace X] [MulAction G X] [MeasurableConstSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ] [Group Γ] [Countable Γ] [Fintype ι] [Fintype κ] (φ : Γ →* G) (ρ : X → ℝ) (β : ι → G) (α : κ → G) (e : Γ × ι ≃ κ × Γ) (P : ι → X → ℂ) (Q : κ → X → ℂ), Measurable ρ → (∀ x, 0 ≤ ρ x) → (∀ x, HasSum (fun γ : Γ => ρ (φ γ • x)) 1) → (∀ p, φ p.1 * β p.2 = α (e p).1 * φ (e p).2) → (∀ p x, P p.2 x = Q (e p).1 (φ (e p).2 • x)) → (∀ i, Integrable (fun x => (ρ x : ℂ) * P i x) μ) → (∀ j, AEStronglyMeasurable (Q j) μ) → (∀ j, Integrable (fun x => (ρ x : ℂ) * Q j ((α j)⁻¹ • x)) μ) ∧ ∑ i, ∫ x, (ρ x : ℂ) * P i x ∂μ = ∑ j, ∫ x, (ρ x : ℂ) * Q j ((α j)⁻¹ • x) ∂μ := by
  first | exact @GlobalTheory.EisM.abstract_double_coset_adjoint | exact GlobalTheory.EisM.abstract_double_coset_adjoint | (intros; apply GlobalTheory.EisM.abstract_double_coset_adjoint <;> assumption)
