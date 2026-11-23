module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.PullbackSquarePartialSum
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

def jj (j : (pullExt f E).ChartIdx) : E.ChartIdx := fun k => j k PUnit.unit

lemma chart_le (j : (pullExt f E).ChartIdx) :
    (pullExt f E).chart j ≤ pullback.fst E.B.hom f ⁻¹ᵁ E.chart (jj f E j) := by
  intro y hy
  have hy' : y ∈ ((⨅ k, ((pullExt f E).O ((pullExt f E).basis k)).L.U (j k) :
      (pullExt f E).B.left.Opens) : Set _) := hy
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hy'
  show (pullback.fst E.B.hom f).base y ∈ ((⨅ k, (E.O (E.basis k)).L.U (jj f E j k) : E.B.left.Opens) : Set _)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro k
  exact Set.mem_iInter.1 (hy' k) PUnit.unit

variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

lemma pre_le (j : (pullExt f E).ChartIdx) :
    (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (jj f E j)) := by
  intro y hy
  have h1 := chart_le f E j hy
  have e₁ := congrArg (fun g => g y) (qB_h f d.q)
  simp only [Scheme.Hom.comp_apply] at e₁
  exact (congrArg (· ∈ E.chart (jj f E j)) e₁).mp h1

def uB (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    Γ(((Over.pullback f).obj G).left, (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j)ˣ :=
  res (pre_le f E d j) (pullU (pullback.fst G.hom f) _ (d.u (jj f E j) k))

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
