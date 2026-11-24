module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.Analysis.Convex.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_cut :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F) (f : F →L[ℝ] ℝ) (u : ℝ), Convex ℝ X → (∀ i, Convex ℝ (A i)) → (nerve X A = fun n => nerve (X ∩ {x | f x ≤ u}) A n ∪ nerve (X ∩ {x | u ≤ f x}) A n) ∧ (nerve (X ∩ {x | f x = u}) A = fun n => nerve (X ∩ {x | f x ≤ u}) A n ∩ nerve (X ∩ {x | u ≤ f x}) A n) := by
  intro I F _ _ X A f u hX hA
  constructor
  · funext n
    ext t
    simp only [nerve, Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, ht⟩
      rcases le_total (f x) u with h | h
      · exact Or.inl ⟨x, ⟨hx, h⟩, ht⟩
      · exact Or.inr ⟨x, ⟨hx, h⟩, ht⟩
    · rintro (⟨x, ⟨hx, _⟩, ht⟩ | ⟨x, ⟨hx, _⟩, ht⟩) <;> exact ⟨x, hx, ht⟩
  · funext n
    ext t
    simp only [nerve, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hx, hfx⟩, ht⟩
      exact ⟨⟨x, ⟨hx, hfx.le⟩, ht⟩, ⟨x, ⟨hx, hfx.ge⟩, ht⟩⟩
    · rintro ⟨⟨x, ⟨hx, h1⟩, ht⟩, ⟨y, ⟨hy, h2⟩, ht'⟩⟩
      rcases lt_or_ge (f x) (f y) with hd | hd
      · have hd' : 0 < f y - f x := sub_pos.2 hd
        have hne : f y - f x ≠ 0 := hd'.ne'
        have ha0 : 0 ≤ (f y - u) / (f y - f x) := div_nonneg (by linarith) hd'.le
        have hb0 : 0 ≤ (u - f x) / (f y - f x) := div_nonneg (by linarith) hd'.le
        have hab : (f y - u) / (f y - f x) + (u - f x) / (f y - f x) = 1 := by
          rw [← add_div, div_eq_one_iff_eq hne]
          ring
        refine ⟨((f y - u) / (f y - f x)) • x + ((u - f x) / (f y - f x)) • y,
          ⟨hX hx hy ha0 hb0 hab, ?_⟩, fun j => hA _ (ht j) (ht' j) ha0 hb0 hab⟩
        rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      · exact ⟨x, ⟨hx, le_antisymm h1 (h2.trans hd)⟩, ht⟩
