module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.RepresentationTheory.Semisimple
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private theorem subrepresentation_isCompl_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (p q : Subrepresentation ρ) :
    IsCompl p q ↔ IsCompl p.toSubmodule q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    Subrepresentation.ext_iff, Subrepresentation.ext_iff, Subrepresentation.toSubmodule_inf,
    Subrepresentation.toSubmodule_sup]
  rfl


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
theorem _root_.GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), _root_.GlobalTheory.ClassFin.SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  intro ι _ _ G _ V _ _ ρ b
  set e := b.equivFun
  have he : ∀ (g : G) (v : V), (LinearMap.toMatrix b b (ρ g)).mulVec (e v) = e (ρ g v) := fun g v =>
    LinearMap.toMatrix_mulVec_repr b b (ρ g) v

  have hmap : ∀ p : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p) →
      ∀ M ∈ Set.range (fun g => LinearMap.toMatrix b b (ρ g)), ∀ w ∈ p.map (e : V →ₗ[ℂ] (ι → ℂ)),
        M.mulVec w ∈ p.map (e : V →ₗ[ℂ] (ι → ℂ)) := by
    rintro p hp _ ⟨g, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hp g hv, (he g v).symm⟩
  have hcomap : ∀ W : Submodule ℂ (ι → ℂ),
      (∀ M ∈ Set.range (fun g => LinearMap.toMatrix b b (ρ g)), ∀ w ∈ W, M.mulVec w ∈ W) →
        ∀ (g : G) ⦃v : V⦄, v ∈ W.comap (e : V →ₗ[ℂ] (ι → ℂ)) → ρ g v ∈ W.comap (e : V →ₗ[ℂ] (ι → ℂ)) := by
    intro W hW g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact hW _ ⟨g, rfl⟩ _ hv
  let Φ := Submodule.orderIsoMapComap e
  constructor
  · intro hS
    refine ⟨fun p => ?_⟩
    obtain ⟨W', hW', hc⟩ := hS _ (hmap p.toSubmodule p.apply_mem_toSubmodule)
    refine ⟨⟨W'.comap (e : V →ₗ[ℂ] (ι → ℂ)), hcomap W' hW'⟩, ?_⟩
    rw [subrepresentation_isCompl_iff]
    have := (Φ.symm.isCompl_iff).1 hc
    simpa [Φ, Submodule.comap_map_eq_of_injective e.injective] using this
  · intro hC W hW
    obtain ⟨q, hq⟩ := hC.exists_isCompl ⟨W.comap (e : V →ₗ[ℂ] (ι → ℂ)), hcomap W hW⟩
    refine ⟨q.toSubmodule.map (e : V →ₗ[ℂ] (ι → ℂ)), hmap _ q.apply_mem_toSubmodule, ?_⟩
    rw [subrepresentation_isCompl_iff] at hq
    have := (Φ.isCompl_iff).1 hq
    simpa [Φ, Submodule.map_comap_eq_of_surjective e.surjective] using this

end GlobalTheory.ClassFin
