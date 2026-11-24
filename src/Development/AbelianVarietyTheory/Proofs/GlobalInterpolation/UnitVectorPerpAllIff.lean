module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.UnitVectorOrthogonal
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace GlobalTheory.UnitVectorPerpCompare

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem selfDual_iff (W : HSpace E) (L : Submodule (𝓞 E) W.V) :
    UnitVectorOrthogonal.IsSelfDualLat W L ↔ SelfDualLatticeComplements.IsSelfDualLattice W L := Iff.rfl

theorem ofKind_iff (W : HSpace E) (M P Q : ℕ) :
    UnitVectorOrthogonal.OfKind W M P Q ↔ SelfDualLatticeComplements.OfKind W M P Q :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

theorem hasComplement_iff (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) :
    UnitVectorOrthogonal.HasComplement W x M' P' Q' ↔ SelfDualLatticeComplements.HasComplement W x M' P' Q' := by
  constructor
  · rintro ⟨L, hL, hx, hs, W', ι, hk, hi, hr, hm⟩
    exact ⟨L, W', ι, (selfDual_iff W L).1 hL, hx, (ofKind_iff _ _ _ _).1 hk, hi, hr, hm, hs⟩
  · rintro ⟨L, W', ι, hL, hx, hk, hi, hr, hm, hs⟩
    exact ⟨L, (selfDual_iff W L).2 hL, hx, hs, W', ι, (ofKind_iff _ _ _ _).2 hk, hi, hr, hm⟩


omit [NumberField E] [StarRing E] in
theorem forall_step_iff (P Q : ℕ) (C : E → ℕ → ℕ → Prop) :
    (∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' → C β P' Q') ↔
      (1 ≤ P → C 1 (P - 1) Q) ∧ (1 ≤ Q → C (-1) P (Q - 1)) := by
  constructor
  · intro h
    exact ⟨fun hP => h _ _ _ (Or.inl ⟨rfl, hP, rfl, rfl⟩),
      fun hQ => h _ _ _ (Or.inr ⟨rfl, hQ, rfl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ β P' Q' (⟨rfl, hP, rfl, rfl⟩ | ⟨rfl, hQ, rfl, rfl⟩)
    · exact h1 hP
    · exact h2 hQ

theorem conclusion_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

theorem over_iff : UnitVectorOrthogonal.UnitVectorPerpOver E ↔ SelfDualLatticeComplements.ExistsPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusion_iff W M P Q

end General

theorem unitVectorPerp_iff (D : D7) : UnitVectorOrthogonal.UnitVectorPerp D ↔ SelfDualLatticeComplements.UnitVectorPerp D :=
  @over_iff D.host.E _ _ D.host.cmStar

end GlobalTheory.UnitVectorPerpCompare

end
