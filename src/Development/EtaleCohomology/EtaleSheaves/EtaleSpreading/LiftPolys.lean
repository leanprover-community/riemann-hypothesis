module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Category.Ring.FilteredColimits
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

@[expose] public section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SpreadPf.Lift

variable {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}

theorem lift_elem (hc : IsColimit c) (a : c.pt) : ∃ (j : J) (x : D.obj j), c.ι.app j x = a := by
  have hc' := isColimitOfPreserves (forget CommRingCat.{0}) hc
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc' a
  exact ⟨j, x, hx⟩

theorem map_ι_map {σ : Type} {j k : J} (u : j ⟶ k) (q : MvPolynomial σ (D.obj j)) :
    MvPolynomial.map (c.ι.app k).hom (MvPolynomial.map (D.map u).hom q) = MvPolynomial.map (c.ι.app j).hom q := by
  rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, c.w]

theorem lift_poly (hc : IsColimit c) {σ : Type} (p : MvPolynomial σ c.pt) :
    ∃ (j : J) (q : MvPolynomial σ (D.obj j)), MvPolynomial.map (c.ι.app j).hom q = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨j, x, hx⟩ := lift_elem hc a
    exact ⟨j, MvPolynomial.C x, by simp [hx]⟩
  | add p q hp hq =>
    obtain ⟨j₁, q₁, h₁⟩ := hp
    obtain ⟨j₂, q₂, h₂⟩ := hq
    refine ⟨IsFiltered.max j₁ j₂, MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom q₁ +
      MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂, ?_⟩
    rw [map_add (f := _), map_ι_map, map_ι_map, h₁, h₂]
  | mul_X p i hp =>
    obtain ⟨j, q, h⟩ := hp
    exact ⟨j, q * MvPolynomial.X i, by simp [h]⟩

theorem lift_polys (hc : IsColimit c) {σ : Type} : ∀ (m : ℕ) (p : Fin m → MvPolynomial σ c.pt),
    ∃ (j : J) (q : Fin m → MvPolynomial σ (D.obj j)), ∀ i, MvPolynomial.map (c.ι.app j).hom (q i) = p i := by
  intro m
  induction m with
  | zero =>
    intro p
    exact ⟨IsFiltered.nonempty.some, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro p
    obtain ⟨j₁, q₁, h₁⟩ := ih (fun i => p i.succ)
    obtain ⟨j₂, q₂, h₂⟩ := lift_poly hc (p 0)
    refine ⟨IsFiltered.max j₁ j₂, Fin.cons (MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂)
      (fun i => MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom (q₁ i)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; rw [map_ι_map, h₂]
    · simp only [Fin.cons_succ]; rw [map_ι_map, h₁]

end LateralTheory.E.SpreadPf.Lift
