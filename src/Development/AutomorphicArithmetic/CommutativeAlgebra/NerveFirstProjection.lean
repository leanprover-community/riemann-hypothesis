module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A)
    (h : Ideal.span (Set.range v) = ⊤) (a b : A) (hab : ∀ j, a * v j = b * v j) : a = b := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range v) := by rw [h]; trivial
  have key : ∀ c ∈ Ideal.span (Set.range v), (a - b) * c = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [sub_mul, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have h2 := key 1 h1
  rw [mul_one] at h2
  exact sub_eq_zero.1 h2

private theorem fam_inj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (x y : Fin (m + 1) → (L2 D d).obj A)
    (hx : ∀ i j, (L2 D d).rel (x i) (x j)) (hy : ∀ i j, (L2 D d).rel (y i) (y j))
    (h1 : ∀ i, (fstV D d).app A (x i) = (fstV D d).app A (y i))
    (h2 : (x 0).1.1.2 (Fin.last d) = (y 0).1.1.2 (Fin.last d)) : x = y := by
  have hv : ∀ i (j : Fin d), (x i).1.1.2 j.castSucc = (y i).1.1.2 j.castSucc :=
    fun i j => congrFun (congrArg (fun z => z.1.2) (h1 i)) j
  have hr : ∀ i, (x i).1.1.1 = (y i).1.1.1 := fun i => congrArg (fun z => z.1.1) (h1 i)
  refine funext fun i => Subtype.ext (Subtype.ext (Prod.ext (hr i) (funext fun j => ?_)))
  obtain ⟨-, u, hu⟩ := hx i 0
  obtain ⟨-, u', hu'⟩ := hy i 0
  have huu : (u : A) = u' := by
    refine unit_unique (fun j : Fin d => (x 0).1.1.2 j.castSucc) (x 0).2 _ _ fun j => ?_
    have e1 : (x i).1.1.2 j.castSucc = (u : A) * (x 0).1.1.2 j.castSucc := congrFun hu _
    have e2 : (y i).1.1.2 j.castSucc = (u' : A) * (y 0).1.1.2 j.castSucc := congrFun hu' _
    change (u : A) * (x 0).1.1.2 j.castSucc = (u' : A) * (x 0).1.1.2 j.castSucc
    rw [← e1, hv i j, e2, hv 0 j]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have e1 : (x i).1.1.2 (Fin.last d) = (u : A) * (x 0).1.1.2 (Fin.last d) := congrFun hu _
    have e2 : (y i).1.1.2 (Fin.last d) = (u' : A) * (y 0).1.1.2 (Fin.last d) := congrFun hu' _
    change (x i).1.1.2 (Fin.last d) = (y i).1.1.2 (Fin.last d)
    rw [e1, e2, huu, h2]
  · exact hv i j
