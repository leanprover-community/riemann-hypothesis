module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemOfMemImage
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CechMV

theorem exists_extend_of_pull_inf_eq_zero (X : Scheme.{0}) (W V : X.Opens) (p : Pic W.toScheme)
    (hp : pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0) :
    ∃ q : Pic (W ⊔ V).toScheme, pull (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) q = p := by
  obtain ⟨N, hN, rfl⟩ := cls_surj p
  have sq : IsPullback (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) (X.homOfLE (inf_le_right : W ⊓ V ≤ V))
      (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) (X.homOfLE (le_sup_right : V ≤ W ⊔ V)) :=
    isPullback_opens_inf_le le_sup_left le_sup_right
  have hcov : Set.range (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) ∪
      Set.range (X.homOfLE (le_sup_right : V ≤ W ⊔ V)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases x.2 with h | h
    · refine Or.inl ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext (by simp [Scheme.homOfLE_apply])
    · refine Or.inr ⟨⟨x.1, h⟩, ?_⟩
      exact Subtype.ext (by simp [Scheme.homOfLE_apply])
  have hT := LB.isLB_triv V.toScheme
  have iso : LBIso (N.pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)))
      ((LB.triv V.toScheme).pull (X.homOfLE (inf_le_right : W ⊓ V ≤ V))) := by
    refine (cls_eq_iff (pull_isLB hN _) (pull_isLB hT _)).1 ?_
    rw [cls_pull hN _ (pull_isLB hN _), cls_pull hT _ (pull_isLB hT _), hp]
    exact (map_zero (pull (X.homOfLE (inf_le_right : W ⊓ V ≤ V)))).symm
  obtain ⟨L, hL, e, -⟩ := GlobalTheory.GlueTwoLB.glue _ _ _ _ _ _ _ _ N (LB.triv V.toScheme) inferInstance inferInstance
    sq hcov hN hT iso
  exact ⟨cls L hL, ((cls_eq_iff hN (pull_isLB hL _)).2 e).symm⟩

end GlobalTheory.CompanionTheory.CechMV
