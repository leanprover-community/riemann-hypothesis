module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.MatEndPull

theorem matEnd_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr pr' a b f₁ f₁' hB hC hpr e hf
  obtain ⟨hm, hw⟩ := hf
  haveI := hm
  refine ⟨isMonHom_lift hB e, fun w => ?_⟩
  apply ext_of_pb hC
  have key : (f₁' ≫ pr' w).left ≫ χ = φB ≫ (f₁ ≫ pr w).left := by
    rw [Over.comp_left, Category.assoc, hpr, ← Category.assoc, e, Category.assoc, ← Over.comp_left]
  rw [key, hw w]
  split_ifs
  · exact (hpr b).symm
  · rw [_root_.ReciprocityTheory.ChartRestriction.G.Chart.one_left', _root_.ReciprocityTheory.ChartRestriction.G.Chart.one_left', ← Category.assoc, hB.1.w, Category.assoc, Category.assoc,
      _root_.ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hC]

end GlobalTheory.MatEndPull

end
