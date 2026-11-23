module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem splitTorus_hom_eq_one_of_no_cocharacter :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) →
      ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  intro S B _ X _ _ _ h u hu
  classical
  let b := Module.Free.chooseBasis ℤ X
  let l : _ → (X →+ ULift.{0} ℤ) := fun i =>
    (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  let c : _ → (ULift.{0} ℤ →+ X) := fun i =>
    (zmultiplesHom X (b i)).comp (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom
  have h1 : ∀ i, SplitTorus.torusMap S ((c i).comp (l i)) ≫ u = 1 := fun i => by
    have e : SplitTorus.torusMap S (l i) ≫ u = 1 := h _ (inferInstanceAs
      (IsMonHom (SplitTorus.torusMap S (l i) ≫ u)))
    rw [SplitTorus.torusMap_comp, Category.assoc, e, MonObj.comp_one]
  have h2 : ∀ s : Finset (Module.Free.ChooseBasisIndex ℤ X),
      SplitTorus.torusMap S (∑ i ∈ s, (c i).comp (l i)) ≫ u = 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, SplitTorus.torusMap_zero, MonObj.one_comp]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, SplitTorus.torusMap_add, MonObj.mul_comp, h1, ih, _root_.mul_one]
  have h3 : (∑ i, (c i).comp (l i)) = AddMonoidHom.id X := by
    ext x
    rw [AddMonoidHom.finsetSum_apply]
    simpa [c, l] using b.sum_repr x
  have := h2 Finset.univ
  rwa [h3, SplitTorus.torusMap_id, Category.id_comp] at this

end GlobalTheory.SS
