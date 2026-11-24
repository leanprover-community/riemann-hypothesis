module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

lemma res_res_pull {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem triv_pull_of_isPullGen : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → Triv (M.pull p) := by
  intro X Y p M e he
  refine ⟨⟨fun j => res (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit) (e (j PUnit.unit))⟩, fun i j => ?_⟩
  have gg : (M.pull p).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
      (pullU p _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
    (Fintype.prod_unique (fun k : PUnit => (res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i k))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j k)))
      (pullU p _ (M.g (i k) (j k)))) ^ (1 : ℤ))).trans (zpow_one _)
  rw [gg]
  have h := he (i PUnit.unit) (j PUnit.unit) (LB.wchart M (fun _ : PUnit => p) i ⊓ LB.wchart M (fun _ : PUnit => p) j)
    (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
    (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit))
    (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
  refine (res_res_pull _ _ _).trans (h.trans ?_)
  exact congrArg _ (res_res_pull _ _ _).symm

end GlobalTheory.CharKer
