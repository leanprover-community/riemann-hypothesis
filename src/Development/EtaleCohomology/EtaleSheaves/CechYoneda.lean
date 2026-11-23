module

public import Development.EtaleCohomology.EtaleSheaves.CechSigmaOf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Yo
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

def eW {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    yoneda.obj (widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≅
      widePullback (yoneda.obj B) (fun _ : Fin (n + 1) => yoneda.obj A) (fun _ => yoneda.map p) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

theorem eW_π {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (eW p n).hom ≫ WidePullback.π _ i = yoneda.map (WidePullback.π _ i) := by
  simp only [eW, Iso.trans_hom, WidePullback.π]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem eW_base {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    (eW p n).hom ≫ WidePullback.base _ = yoneda.map (WidePullback.base _) := by
  simp only [eW, Iso.trans_hom, WidePullback.base]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem cechYoneda : CechYoneda := by
  intro A B C D p q s n
  refine ⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩
  apply WidePullback.hom_ext
  · intro i
    simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_π]
    erw [← Category.assoc, eW_π, Category.assoc, eW_π]
    change yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]
  · simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_base]
    erw [← Category.assoc, eW_base, Category.assoc, eW_base]
    change yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]

end LateralTheory.E.CechSigma_xy1Pf_Yo
