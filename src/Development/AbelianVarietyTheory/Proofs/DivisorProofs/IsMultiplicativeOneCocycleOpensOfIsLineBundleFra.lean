module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.FrameCoc

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(X, U)ˣ) :
    res h (res h' x) = res (h.trans h') x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCoc_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → IsFrame L V hV u → IsCoc V hV u := by
  intro X C _ V hV L u hL hF T T' T'' a b
  obtain ⟨τ, -, hτ⟩ := hF
  have key : ∀ m : L.ι, res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (u T T'' (a ≫ b)) =
      res (inf_le_left : V T'' ⊓ L.U m ≤ V T'') (res (hV b) (u T T' a) * u T' T'' b) := by
    intro m
    have h1 := hτ T T'' (a ≫ b) m
    have h2 := congrArg (res (inf_le_inf_right (L.U m) (hV b))) (hτ T T' a m)
    have h3 := hτ T' T'' b m
    rw [res_res', map_mul, res_res', h3] at h2
    rw [h1] at h2
    apply mul_right_cancel (b := τ T'' m)
    rw [h2, map_mul, res_res', ← _root_.mul_assoc]
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun m => V T'' ⊓ L.U m) (V T'') (fun m => homOfLE inf_le_left) ?_ _ _ ?_
  · rw [← inf_iSup_eq, hL.cover, inf_top_eq]
  · intro m
    exact congrArg Units.val (key m)

end GlobalTheory.LBObs.FrameCoc
