module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AffInj

theorem inr_injective_of_isPushout {R A K P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : Function.Injective φ.hom)
    (hψ : ψ.hom.Flat) : Function.Injective inr.hom := by
  algebraize [φ.hom, ψ.hom]
  let e := (CommRingCat.isPushout_tensorProduct R A K).isoIsPushout _ _ H
  have h1 : inr = _ ≫ e.hom :=
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A K) H).symm
  rw [h1, CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom).comp ?_
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := K)
    (Algebra.linearMap R A) hφ
  intro a b hab
  apply (TensorProduct.lid R K).symm.injective
  apply hinj
  simpa using hab

end GlobalTheory.AffInj

namespace GlobalTheory.AffInj

theorem app_injective_of_isPullback (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R)
    (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S) (hπ : IsProper π) (hy : Flat y)
    (H : IsPullback p q y π) (hinj : Function.Injective π.appTop.hom) (V : Y.Opens)
    (hV : IsAffineOpen V) : Function.Injective (p.app V).hom := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have hUY : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hST : V ≤ y ⁻¹ᵁ ⊤ := le_top
  have hSX : (⊤ : S.Opens) ≤ π ⁻¹ᵁ ⊤ := le_top
  let σ := pushoutSection H.flip hST hSX hUY
  have hm : Mono σ := mono_pushoutSection_of_isCompact_of_flat_right H.flip hST hSX hUY
    (isAffineOpen_top _) hV (by simpa using isCompact_univ)
  have hσ : Function.Injective σ.hom := (ConcreteCategory.mono_iff_injective_of_preservesPullback σ).mp hm
  have h1 : pushout.inr _ _ ≫ σ = p.appLE V (p ⁻¹ᵁ V) le_rfl := pushout.inr_desc _ _ _
  have hφ : Function.Injective (π.appLE ⊤ ⊤ hSX).hom := by
    have e : π.appLE ⊤ ⊤ hSX = π.appTop := (Scheme.Hom.app_eq_appLE π (U := ⊤)).symm
    rw [e]; exact hinj
  have hinr := inr_injective_of_isPushout (IsPushout.of_hasPushout (π.appLE ⊤ ⊤ hSX)
    (y.appLE ⊤ V hST)) hφ (y.flat_appLE (isAffineOpen_top _) hV _)
  have h2 : p.app V = p.appLE V (p ⁻¹ᵁ V) le_rfl := Scheme.Hom.app_eq_appLE p
  rw [h2, ← h1, CommRingCat.hom_comp, RingHom.coe_comp]
  exact hσ.comp hinr

end GlobalTheory.AffInj
