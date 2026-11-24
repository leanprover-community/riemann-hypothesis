module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section FamPr

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R}

theorem famφB_pr (pD : IsPowDeg D' D j) (α' : D'.X) (i : Fin j) (a : Fin 4) :
    D'.famφB α' a ≫ (pD.pw.pr i).left = (pD.pw.pr i).left ≫ D.famφB (pD.xe α' i) a := by
  haveI := pD.pw.hom i
  have hc := pD.c_pr α' i
  fin_cases a <;>
    simp [DegPre.famφB, ← Over.comp_left, padd, hc, IsMonHom.mul_hom, IsMonHom.one_hom]
  all_goals
    first
    | (rw [← Over.comp_left]; congr 1;
        simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])
    | (congr 1; simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_toUnit_assoc])

def boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) (α' : D'.X) : D'.SecB k α' :=
  secOfIso (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _)

theorem isBoxFamB_boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) :
    IsBoxFamB pD k (boxFamB pD k f) f := by
  intro α'
  refine ⟨famφB_pr pD α', fun jN jM => ?_⟩
  set V := LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓ LB.wchart D'.P.L (D'.famφB α') jM with hVdef
  have hVab : V ≤ LB.wchart D'.P.L (D'.famφB α') jM ⊓ LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN :=
    fun _ hy => ⟨hy.2, hy.1⟩
  have hspec := congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _) jM jN)
  erw [rs_rs] at hspec
  have hspec2 := hspec.trans (isoCand_rs (LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i))) jM jN hVab)
  have hVd : V ≤ (LB.div (LB.LinComb (boxLB D.P.L pD.pw.pr) (D'.famφB α') (DegPre.famε k))
      (LB.LinComb D'.P.L (D'.famφB α') (DegPre.famε k))).U (jN, jM) := fun _ hy => ⟨hy.1, hy.2⟩
  have hu : res hVd ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) =
      @id (Γ(D'.P.A.left, V)ˣ) ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) :=
    res_refl' _
  have key := unit_cancel _ _ _ _ hspec2 hu
  refine key.trans ?_
  simp only [boxSecGen, boxSecGenF]
  refine (map_prod ((D'.P.A.left.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

end FamPr

end ReciprocityTheory.ChartRestriction.G.DVR
