module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finpt_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  intro R _ _ _ hR Z π _ k hk
  obtain ⟨⟨hN, -, -, hC⟩, -⟩ := hR
  haveI := hN
  haveI := hC
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let i : Spec Γ(Z, ⊤) ≅ Z := Z.isoSpec.symm
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (i.hom ≫ π)
  have h₁ : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ i.inv)
  have hc : θ ≫ ψ = CommRingCat.ofHom (algebraMap R (Kb R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hθ, Category.assoc, i.inv_hom_id_assoc, hk]
    simp only [TF, jFK, jK, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let _ : Algebra R Γ(Z, ⊤) := θ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := h₁
  let φ : Γ(Z, ⊤) →ₐ[R] Kb R := ⟨ψ.hom, fun r => congr(($hc).hom r)⟩
  let S : Subalgebra R (Kb R) := φ.range
  have hfin : Module.Finite R S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hloc : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  refine ⟨S, hfin, hloc, spMap (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ i.hom, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (φ.rangeRestrict.commutes r)
  · rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ CommRingCat.ofHom (S.val : S →+* Kb R) = ψ := by
      ext b; rfl
    rw [this, hψ, Category.assoc, i.inv_hom_id, Category.comp_id]

end GlobalTheory.Mum
