module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

namespace GlobalTheory.FiniteFlatLocal

theorem exists_finFree_local : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  intro S Z z h1 h2 h3 s
  obtain ⟨V, hV, hsV, -, hF⟩ := GlobalTheory.FiniteAmpleFP.exists_finFree_app_fp z (x := s) (U := ⊤) trivial
  have hZ : IsAffineOpen (z ⁻¹ᵁ V) := hV.preimage z
  letI : Algebra Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := (z.app V).hom.toAlgebra
  have hfin : Module.Finite Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.1
  have hfree : Module.Free Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.2
  refine ⟨V, Γ(S, V), Γ(Z, z ⁻¹ᵁ V), inferInstance, inferInstance, inferInstance, hfree, hfin,
    hV.isoSpec, hZ.isoSpec, hsV, ?_⟩
  have e := IsAffineOpen.SpecMap_appLE_fromSpec z hV hZ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at e
  rw [← cancel_mono (hV.isoSpec.inv ≫ V.ι)]
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, ← IsAffineOpen.isoSpec_hom_fromSpec hZ, Category.assoc, ← e]
  rfl

end GlobalTheory.FiniteFlatLocal
