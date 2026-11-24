module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TypeSum in
theorem GlobalTheory.TypeSum.typAdd_of_discreteSeries : ∀ D : D7, (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → TypAdd D := by
  intro D hex huniq θ hθ V hV τ S hS
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  refine ⟨(GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2 ?_, fun φ φ' _ _ h h' => ?_⟩
  · obtain ⟨H, i1, i2, σ, hσ⟩ := hex _ ε₀ lam₀ hP₀
    obtain ⟨P, h1, h2⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
    exact ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, h1, h2⟩
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hσ, hP, hG, hx⟩ := h
  obtain ⟨H', j1, j2, σ', lam', ε', P', hE', hσ', hP', hG', hx'⟩ := h'
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE' hE₀
  obtain ⟨U, hU⟩ := huniq _ _ _ hP₀ H' H σ' σ hσ' hσ
  refine ⟨H, i1, i2, σ, _, _, P, hE, hσ, hP, hG, fun x => ?_⟩
  exact hasTypeAll_iff.1 (hasTypeAll_add_of_equiv hσ.2.2.1 U hU hP hP' hG hG'
    (f := fun g => φ (x * atTau θ V τ g)) (f' := fun g => φ' (x * atTau θ V τ g))
    (hasTypeAll_iff.2 (hx x)) (hasTypeAll_iff.2 (hx' x)))
