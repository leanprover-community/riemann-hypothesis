module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.DiagPow

theorem eSec_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  unfold eSec
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift]
  congr 1
  rw [Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]

theorem diagPow_isLB_rigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d →
      (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  intro S A _ _ Q hQ d hd
  obtain ⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩ := hQ
  have hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hQL _
  have hD : (diagPow A Q d).IsLB := LB.isLB_linComb hQL _ _
  have hcls : CechPic.cls _ hD = d • CechPic.cls _ hM := by
    refine (CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_
    rw [Fintype.sum_unique, CechPic.cls_pull hQL _ hM]
    exact natCast_zsmul _ d
  refine ⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩
  have h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 :=
    (CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩
  refine (CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_
  rw [CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag,
    CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]

end GlobalTheory.ActFin.DiagPow
