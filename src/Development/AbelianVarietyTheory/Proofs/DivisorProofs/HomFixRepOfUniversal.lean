module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
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

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open Opposite

namespace GlobalTheory.EndLoc.HomFixGlue

theorem pullPull_mem {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) (J : PUnit → PUnit → M.ι) (y : Z')
    (hy : y ∈ ((M.pull F').pull G').U J) :
    h y ∈ ((M.pull F).pull G).U (fun _ => fun _ => J PUnit.unit PUnit.unit) := by
  have h1 := mem_pull.1 (mem_pull.1 hy)
  have e : F (G (h y)) = F' (G' y) := by
    have := congrArg (fun k => k y) hc
    simpa using this.symm
  exact mem_pull.2 (mem_pull.2 (by rw [e]; exact h1))

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) : ChartPull ((M.pull F').pull G') ((M.pull F).pull G) h where
  idx J := fun _ => fun _ => J PUnit.unit PUnit.unit
  le J y hy := pullPull_mem M F G F' G' h hc J y hy
  g y J J' hj hj' := by
    have a1 := gm_pull_g (M.pull F') G' (𝟙 _) y J J' hj hj'
    have a2 := gm_pull_g M F' (𝟙 _ ≫ G') y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have m1 := pullPull_mem M F G F' G' h hc J y hj
    have m2 := pullPull_mem M F G F' G' h hc J' y hj'
    have b1 := gm_pull_g (M.pull F) G h y _ _ m1 m2
    have b2 := gm_pull_g M F (h ≫ G) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 m1) (mem_pull.1 m2)
    rw [a1, a2, b1, b2]
    have e : (𝟙 _ ≫ G') ≫ F' = (h ≫ G) ≫ F := by simp [hc]
    rw [e]

section
variable {S : Scheme.{0}}

variable (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

end

end GlobalTheory.EndLoc.HomFixGlue
