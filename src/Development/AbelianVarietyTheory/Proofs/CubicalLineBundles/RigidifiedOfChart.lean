module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChartRig

variable {X Y : Scheme.{0}}

theorem res_pullU_eq (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U x) = Units.map (f.appLE U V h).hom.toMonoidHom x := by
  ext
  rfl

theorem res_res_pullU (f : Y ⟶ X) (U : X.Opens) (V W : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ V)
    (x : Γ(X, U)ˣ) : res h' (res h (pullU f U x)) = res (h'.trans h) (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl

theorem res_pullU_res (f : Y ⟶ X) (U U' : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U' (res h' x)) = res h'' (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U' V h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem exists_gen_pull (L : LB X) (f : Y ⟶ X) (i : L.ι) (hL : L.IsLB) (hi : ⊤ ≤ f ⁻¹ᵁ L.U i) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  have le1 : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => f) j ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U i) :=
    fun j => le_inf (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit) (le_top.trans hi)
  refine ⟨⟨fun j => res (le1 j) (pullU f _ (L.g (j PUnit.unit) i))⟩, fun j k => ?_⟩
  have le2 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => f) k PUnit.unit))
  have le3 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit) ⊓ L.U i) :=
    le_inf le2 (le_top.trans hi)
  have gg : (L.pull f).g j k = res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit))) :=
    (Fintype.prod_unique (fun _ : PUnit =>
      (res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit)))) ^ (1 : ℤ))).trans (zpow_one _)
  have c := congrArg (fun x => res le3 (pullU f _ x)) (hL.cocycle (j PUnit.unit) (k PUnit.unit) i)
  simp only [map_mul] at c
  rw [res_pullU_res f _ _ _ le3 _ le2, res_pullU_res f _ _ _ le3 _ (inf_le_right.trans (le1 k)),
    res_pullU_res f _ _ _ le3 _ (inf_le_left.trans (le1 j))] at c
  rw [gg]
  exact (res_res_pullU f _ _ _ (le1 j) inf_le_left _).trans
    (c.symm.trans (congrArg _ (res_res_pullU f _ _ _ (le1 k) inf_le_right _).symm))

end GlobalTheory.ChartRig
