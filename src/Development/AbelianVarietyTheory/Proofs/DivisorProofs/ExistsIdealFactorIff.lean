module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.KerIdeal

theorem exists_ideal_factor_iff {X Y Z : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y)
    (x₀ : X) :
    ∃ J : Ideal (X.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : X.presheaf.stalk x₀ →+* R'),
      (∃ z : Spec (CommRingCat.of R') ⟶ Z,
        z ≫ i = (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x₀) ≫ f) ↔
        J ≤ RingHom.ker ψ := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd i (X.fromSpecStalk x₀ ≫ f))).1
    inferInstance
  refine ⟨I, fun R' _ ψ => ?_⟩
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ : ∃ w : Spec (CommRingCat.of R') ⟶ pullback i (X.fromSpecStalk x₀ ≫ f),
        w ≫ pullback.fst i (X.fromSpecStalk x₀ ≫ f) = z ∧
          w ≫ pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) :=
      ⟨pullback.lift z (Spec.map (CommRingCat.ofHom ψ)) (hz.trans (Category.assoc _ _ _)),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [he, ← Category.assoc] at hw
    set w' := w ≫ e.hom
    have h3 : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage w' = CommRingCat.ofHom ψ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact hw
    intro a ha
    rw [RingHom.mem_ker]
    have h4 := congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at h4
    exact h4.symm
  · intro hI
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
      pullback.fst i (X.fromSpecStalk x₀ ≫ f), ?_⟩
    have key : Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun a ha => hI ha))) ≫ e.inv ≫
        pullback.snd i (X.fromSpecStalk x₀ ≫ f) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [he, e.inv_hom_id_assoc, ← Spec.map_comp]
      congr 1
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% key]

end GlobalTheory.KerIdeal

namespace GlobalTheory.KerIdeal

theorem kernel_ideal : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B), IsAbelianScheme B → ∀ x₀ : A.left,
    ∃ J : Ideal (A.left.presheaf.stalk x₀), ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      (∃ z : Sp R' ⟶ Sp k, z ≫ (η[B]).left = (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ≫ π.left) ↔
        J ≤ RingHom.ker ψ := by
  intro k _ A B _ π _ x₀
  haveI : IsClosedImmersion (η[B]).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) B.hom _ (Over.w _)
  exact exists_ideal_factor_iff (η[B]).left π.left x₀

end GlobalTheory.KerIdeal
