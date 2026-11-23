module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  first | exact @GlobalTheory.LagLocForm.lagr_local_form | exact GlobalTheory.LagLocForm.lagr_local_form | (intros; apply GlobalTheory.LagLocForm.lagr_local_form <;> assumption)
