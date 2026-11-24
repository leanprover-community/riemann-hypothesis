module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilProdEqOneOfToric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AxisPairing

theorem weilIs_comp_eq_one_of_pull_isGen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left)
    (hA : IsAbelianScheme A) (hP : P.IsLB) (ψ : A ⟶ G2 A) [IsMonHom ψ]
    (hg : ∃ t : (P.pull ψ.left).Gen, t.IsGen) {n : ℤ} {T : Over S} {u v : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs (G2 A) P n (u ≫ ψ) (v ≫ ψ) c) : c = 1 := by
  have hL : (P.pull ψ.left).IsLB := LB.isLB_pull hP ψ.left
  have h0 : GlobalTheory.CechPic.cls _ hL = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 hg
  have hw : LBIso (lbPow (P.pull ψ.left) 1) (P.pull ψ.left) := by
    have hp : (lbPow (P.pull ψ.left) 1).IsLB := LB.isLB_pull hL _
    refine (GlobalTheory.CechPic.cls_eq_iff hp hL).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hL 1 hp, one_smul]
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds hA hL hP ψ hw h
  rw [Nat.cast_one, _root_.mul_one] at h1
  have iso : LBIso (lbPow (P.pull ψ.left) 0) ((P.pull ψ.left).pull (𝟙 A : A ⟶ A).left) := by
    apply (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_pull hL _)).1
    rw [GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_pull hL,
      Over.id_left, GlobalTheory.CechPic.pull_id, h0, zero_smul]
  have h2 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S A A (𝟙 A)
    (P.pull ψ.left) (P.pull ψ.left) 0 n T u v c c hA hA hL hL inferInstance iso
    (by simpa using h1)).2 h1
  simpa using h2

theorem axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  intro S A _ _ P hA hP h₂ h₁ n T u v c
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_id_one A A
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_one_id A A
  have e₁ : ∀ w : T ⟶ A, w ≫ lift (𝟙 A) (1 : A ⟶ A) = lift w 1 := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  have e₂ : ∀ w : T ⟶ A, w ≫ lift (1 : A ⟶ A) (𝟙 A) = lift 1 w := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← e₁ u, ← e₁ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₁ h
  · rw [← e₂ u, ← e₂ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₂ h

end GlobalTheory.AxisPairing
