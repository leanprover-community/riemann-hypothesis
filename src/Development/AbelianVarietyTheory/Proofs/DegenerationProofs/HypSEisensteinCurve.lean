module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.CubeRootAut

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cubeCls_pair {T : Over S} (x y : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y] c = pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem cubeCls_triple {T : Over S} (x y z : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y, z] c = pull (x * y * z).left c - pull (x * y).left c - pull (x * z).left c -
      pull (y * z).left c + pull x.left c + pull y.left c + pull z.left c - pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 3)) ≃ Finset (Fin 3)) _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, y, z] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have p₀ : psum G ![x, y, z] ∅ = 1 := rfl
  have p₁ : psum G ![x, y, z] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y, z] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y, z] {2} = z := _root_.mul_one z
  have p₄ : psum G ![x, y, z] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₅ : psum G ![x, y, z] {0, 2} = x * z := congrArg (x * ·) (_root_.mul_one z)
  have p₆ : psum G ![x, y, z] {1, 2} = y * z := congrArg (y * ·) (_root_.mul_one z)
  have p₇ : psum G ![x, y, z] {0, 1, 2} = x * y * z :=
    (congrArg (fun w => x * (y * w)) (_root_.mul_one z)).trans (_root_.mul_assoc x y z).symm
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have c₁ : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c₂ : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₃ : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₄ : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [c₁, c₂, c₃, c₄, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

end General

end GlobalTheory.ZH.CubeRootAut
