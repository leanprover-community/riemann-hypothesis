module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

namespace GlobalTheory.GelfandLine

variable {G : Type} [Group G]

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.GelfandLine

open GlobalTheory.GelfandLine in
theorem GlobalTheory.fixed_eq_span_of_gelfandPair : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first
  | exact @_root_.GlobalTheory.GroupAverageProjection.main
  | exact _root_.GlobalTheory.GroupAverageProjection.main
  | (apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GroupAverageProjection.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GroupAverageProjection.main ..)
