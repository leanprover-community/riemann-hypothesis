module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem closedImmersion_baseChange_ker_mem_map : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  intro X X' Z Z' p i i' p' h hp hi W hW s hs
  set J : Ideal Γ(X', p ⁻¹ᵁ W) := Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) with hJ
  have hU' : IsAffineOpen (p ⁻¹ᵁ W) := hW.preimage p
  have hZ : IsAffineOpen (i ⁻¹ᵁ W) := hW.preimage i
  have hsurj : Function.Surjective (i.app W).hom := i.app_surjective W hW
  let ψ : Γ(X, W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) := (Ideal.Quotient.mk J).comp (p.app W).hom
  have hker : RingHom.ker (i.app W).hom ≤ RingHom.ker ψ := by
    intro a ha
    simp only [RingHom.mem_ker, ψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : Γ(Z, i ⁻¹ᵁ W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) :=
    (i.app W).hom.liftOfSurjective hsurj ⟨ψ, hker⟩
  have hφ : φ.comp (i.app W).hom = ψ := (i.app W).hom.liftOfRightInverse_comp _ _ _
  let e : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X' :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU'.fromSpec
  let t : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ Z :=
    Spec.map (CommRingCat.ofHom φ) ≫ hZ.fromSpec
  have hw : e ≫ p = t ≫ i := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec p hW hU' le_rfl
    have h2 := IsAffineOpen.SpecMap_appLE_fromSpec i hW hZ le_rfl
    simp only [e, t, Category.assoc, ← h1, ← h2, ← Spec.map_comp, ← Scheme.Hom.app_eq_appLE]
    simp only [← Spec.map_comp_assoc]
    congr 2
    ext x
    exact (RingHom.congr_fun hφ x).symm
  let l := h.lift e t hw
  have hl : l ≫ i' = e := h.lift_fst e t hw
  have hle : (⊤ : (Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).Opens) ≤ e ⁻¹ᵁ (p ⁻¹ᵁ W) := by
    simp [e, Scheme.Hom.comp_preimage, hU'.fromSpec_preimage_self]
  have h0 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = 0 := by
    have key : ∀ (g : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X') (hg : g = e) (hle' : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ W)),
        g.appLE (p ⁻¹ᵁ W) ⊤ hle' = e.appLE (p ⁻¹ᵁ W) ⊤ hle := by
      rintro g rfl _; rfl
    rw [← key (l ≫ i') hl (by rw [hl]; exact hle), Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hs, map_zero]
  have h1 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).inv.hom (Ideal.Quotient.mk J s) := by
    simp only [e, Scheme.Hom.comp_appLE, hU'.fromSpec_app_self]
    rw [Category.assoc]
    erw [Scheme.Hom.map_appLE]
    rw [show ∀ hh, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appLE ⊤ ⊤ hh = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop from fun _ => (Scheme.Hom.app_eq_appLE _).symm]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [h1] at h0
  have h2 : Ideal.Quotient.mk J s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).hom.hom h0
    simpa using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

end GlobalTheory
