module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix GlobalTheory.VacAny


theorem _root_.GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψv : AddChar (Fv F v) ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ (κ : Type) [Fintype κ] (Λ : Submodule (Fv F v) ((κ → Fv F v) × (κ → Fv F v))),
    (∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank (Fv F v) Λ = Fintype.card κ →
    ∀ l₁ l₂ : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₁ (schr ψv w φ) = l₁ φ) →
    (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l₂ (schr ψv w φ) = l₂ φ) →
    (∃ φ ∈ SB (κ → Fv F v), l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), l₁ φ = c * l₂ φ := by
  first | exact @GlobalTheory.LagrInvForm.proportional_at_place | exact GlobalTheory.LagrInvForm.proportional_at_place | (intros; apply GlobalTheory.LagrInvForm.proportional_at_place <;> assumption)
