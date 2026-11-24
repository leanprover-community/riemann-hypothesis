module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CM

private theorem isLieComb_one_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (r : R)
    (v w : epsR R ⟶ G) : IsLieComb ![r] ![v] w ↔ w.left = spMap (epsScaleR r) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨![w], fun i ↦ by rw [Subsingleton.elim i 0]; exact h, by simp⟩

theorem lie_tensor_line :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra O R] (G A : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type)
      [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (v : epsR R ⟶ G),
      Module.Finite O M → Module.Projective O M → IsLieBasis ![v] →
      (∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) →
      ∃ e : TensorProduct O R M → (epsR R ⟶ A), Function.Injective e ∧
        (∀ u, IsTangent u ↔ u ∈ Set.range e) ∧ (∀ z z', e (z + z') = e z * e z') ∧
        (∀ (r : R) z, IsLieComb ![r] ![e z] (e (r • z))) ∧
        ∀ m, e (TensorProduct.tmul O 1 m) = v ≫ t.tmul m := by
  intro R O _ _ _ G A _ _ _ _ a b M _ _ t v _ _ hv hc
  have hτ := fun c ↦ (isLieComb_one_iff _ _ _).mp (hc c)
  let e := t.lieEquivLine b hv hτ
  refine ⟨fun z ↦ (e z).hom, fun z z' h ↦ e.injective (Serre.Lie.ext h), fun u ↦ ⟨fun hu ↦ ?_, ?_⟩,
    fun z z' ↦ by simp only [map_add (f := _), Serre.Lie.hom_add], fun r z ↦ ?_, fun m ↦ ?_⟩
  · exact ⟨e.symm (Serre.Lie.mk b u hu), by simp⟩
  · rintro ⟨z, rfl⟩
    exact (e z).isTangent
  · beta_reduce
    rw [isLieComb_one_iff, map_smul]
    exact Serre.Lie.hom_smul_left r (e z)
  · change (t.lieEquivLine b hv hτ _).hom = _
    rw [Serre.IsTensor.hom_lieEquivLine_tmul, GrpTangent.epsScale_one, Category.id_comp]

end GlobalTheory.CM
