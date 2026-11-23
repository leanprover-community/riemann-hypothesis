module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.EqualityOnPoints

theorem eq_on_points {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) :
    (a x : Y) = b x := by

  set l := pullback.lift a b h with hl
  have hcl : IsClosed (l ⁻¹' Set.range (pullback.diagonal s)) :=
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage l.continuous

  have he : i ≫ l = (i ≫ a) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · rw [hl, Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [hl, Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hi]
  have hsub : Set.range i ⊆ l ⁻¹' Set.range (pullback.diagonal s) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(i ≫ a) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]

  have hall : l x ∈ Set.range (pullback.diagonal s) := by
    have hcl' := hcl.closure_subset_iff.2 hsub
    rw [i.denseRange.closure_range] at hcl'
    exact hcl' (Set.mem_univ x)
  obtain ⟨y, hy⟩ := hall
  have ha : a x = y := by
    have e : (pullback.diagonal s ≫ pullback.fst s s) y = (l ≫ pullback.fst s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_fst, hl, pullback.lift_fst] at e
    simpa using e.symm
  have hb : b x = y := by
    have e : (pullback.diagonal s ≫ pullback.snd s s) y = (l ≫ pullback.snd s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_snd, hl, pullback.lift_snd] at e
    simpa using e.symm
  rw [ha, hb]

end GlobalTheory.EqualityOnPoints
