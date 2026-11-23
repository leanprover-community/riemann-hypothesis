module

public import Mathlib.Algebra.Field.Subfield.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace PositivityTheory.UnitarySelfGeneration

theorem extends_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  intro O F L _ _ _ β θ hcl hu hz
  classical
  set R : Subring F := β.range with hR
  have hk : ∀ a ∈ RingHom.ker β, θ a = 0 := fun a ha => hz a ((RingHom.mem_ker).mp ha)
  let θR : R →+* L :=
    (Ideal.Quotient.lift (RingHom.ker β) θ hk).comp (RingHom.quotientKerEquivRange β).symm.toRingHom
  have hθR : ∀ o : O, θR ⟨β o, o, rfl⟩ = θ o := by
    intro o
    have h : (RingHom.quotientKerEquivRange β).symm ⟨β o, o, rfl⟩ = Ideal.Quotient.mk _ o := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [θR, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h,
      Ideal.Quotient.lift_mk]
  have hunit : ∀ r : nonZeroDivisors R, IsUnit (θR r) := by
    intro r
    obtain ⟨b, hb⟩ := (r : R).2
    have hne : (r : R) ≠ 0 := nonZeroDivisors.ne_zero r.2
    have hr : (r : R) = ⟨β b, b, rfl⟩ := Subtype.ext hb.symm
    rw [hr, hθR]
    apply hu
    intro h0
    apply hne
    rw [hr]
    exact Subtype.ext h0
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  let ι : FractionRing R →+* F := IsFractionRing.lift hinj
  have hsurj : Function.Surjective ι := by
    have h := IsFractionRing.lift_fieldRange (K := FractionRing R) hinj
    have hcl' : Subfield.closure (R : Set F) = ⊤ := by rw [hR, RingHom.coe_range]; exact hcl
    rw [Subring.range_subtype, hcl'] at h
    intro x
    have hx : x ∈ ι.fieldRange := by
      change x ∈ (IsFractionRing.lift hinj : FractionRing R →+* F).fieldRange
      rw [h]
      trivial
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp hx
    exact ⟨y, hy⟩
  let e : FractionRing R ≃+* F := RingEquiv.ofBijective ι ⟨ι.injective, hsurj⟩
  refine ⟨(IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hunit).comp
    e.symm.toRingHom, ?_⟩
  ext o
  have he : e.symm (β o) = algebraMap R (FractionRing R) ⟨β o, o, rfl⟩ := by
    rw [RingEquiv.symm_apply_eq]
    show β o = ι (algebraMap R (FractionRing R) ⟨β o, o, rfl⟩)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he,
    IsLocalization.lift_eq, hθR]

end PositivityTheory.UnitarySelfGeneration
