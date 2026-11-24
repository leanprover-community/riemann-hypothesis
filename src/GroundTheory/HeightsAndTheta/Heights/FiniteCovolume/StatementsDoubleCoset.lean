module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

section Slice

variable {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] [TopologicalSpace G]
  [TopologicalSpace G₁] [TopologicalSpace G₂]

def sliceGroup (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) (K : Subgroup G₂) (s : G₂) : Subgroup G₁ :=
  (Γ ⊓ (Subgroup.prod ⊤ (K.map (MulAut.conj s).toMonoidHom)).comap
      Φ.toMulEquiv.toMonoidHom).map ((MonoidHom.fst G₁ G₂).comp Φ.toMulEquiv.toMonoidHom)

theorem mem_sliceGroup {Φ : G ≃ₜ* G₁ × G₂} {Γ : Subgroup G} {K : Subgroup G₂} {s : G₂} {x : G₁} :
    x ∈ sliceGroup Φ Γ K s ↔ ∃ γ ∈ Γ, s⁻¹ * (Φ γ).2 * s ∈ K ∧ (Φ γ).1 = x := by
  simp only [sliceGroup, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.mem_prod, Subgroup.mem_top, true_and, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst]
  constructor
  · rintro ⟨γ, ⟨hγ, k, hk, hks⟩, rfl⟩
    refine ⟨γ, hγ, ?_, rfl⟩
    have : (Φ γ).2 = s * k * s⁻¹ := by
      have := hks.symm
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
      exact this
    rw [this]
    simpa [mul_assoc] using hk
  · rintro ⟨γ, hγ, hk, rfl⟩
    refine ⟨γ, ⟨hγ, s⁻¹ * (Φ γ).2 * s, hk, ?_⟩, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rfl

end Slice

def DoubleCosetCovolume.Statement (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    Prop :=
  ∀ (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) [Countable Γ] (K : Subgroup G₂) (S : Finset G₂),
    IsCompact (K : Set G₂) → IsOpen (K : Set G₂) →
    (∀ γ ∈ Γ, (Φ γ).1 = 1 → γ = 1) →
    (∀ y : G₂, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, y = (Φ γ).2 * s * k) →
    (∀ s ∈ S, ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], ∃ FD₁ : Set G₁,
      IsFundamentalDomain (sliceGroup Φ Γ K s) FD₁ μ₁ ∧ μ₁ FD₁ < ⊤) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure], ∃ FD : Set G, IsFundamentalDomain Γ FD μ ∧ μ FD < ⊤

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
