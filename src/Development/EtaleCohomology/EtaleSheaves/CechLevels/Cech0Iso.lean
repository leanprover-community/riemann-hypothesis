module

public import Development.EtaleCohomology.EtaleSheaves.CechLevels.CechLevelsOf
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf

def cech0Iso (f : Arrow PSh) : f.cechNerve.obj (op (SimplexCategory.mk 0)) ≅ f.left where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f.hom (fun _ => 𝟙 _) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; rw [Fin.fin_one_eq_zero j]; rw [Category.assoc]; erw [WidePullback.lift_π, Category.comp_id]
    · rw [Category.assoc]; erw [WidePullback.lift_base, Category.id_comp]; exact WidePullback.π_arrow _ 0
  inv_hom_id := by erw [WidePullback.lift_π]

theorem level0 : Level0 := by
  intro A A' _ _ φ I
  refine ⟨Arrow.isoMk (cech0Iso _) (cech0Iso _) ?_⟩
  simp only [cech0Iso, psi, Arrow.mk_hom, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]
  rfl

theorem CechLevels_of' (hL : Levels) : LateralTheory.E.t_E1Cut.CechLevels := CechLevels_of hL level0

end LateralTheory.E.CechLevelsPf
