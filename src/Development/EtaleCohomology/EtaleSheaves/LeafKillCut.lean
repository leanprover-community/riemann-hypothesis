module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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

namespace LateralTheory.E.LeafKillCut

open LateralTheory.E.E4

def LeafOne : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → ∀ x : Ht q (sch.obj C) m i,
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m x = 0

theorem goal_of (hOne : LeafOne) : LateralTheory.E.E4.LeafKill := by
  intro hy q _ Ω _ _ hq C c hc m i hm hfin
  classical
  have key : ∀ s : Finset (Ht q (sch.obj C) m i), ∃ (C' : Scheme.{0}) (γ : C' ⟶ C),
      IsCurve (γ ≫ c) ∧ Surjective γ ∧ ∀ x ∈ s, pl q i γ m x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C, 𝟙 C, by simpa using hc, inferInstance, by simp⟩
    | insert a s ha IH =>
      obtain ⟨C1, γ1, h1, s1, k1⟩ := IH
      obtain ⟨C2, γ2, h2, s2, k2⟩ := hOne hy q Ω hq (γ1 ≫ c) h1 m i hm (pl q i γ1 m a)
      have := s1
      have := s2
      refine ⟨C2, γ2 ≫ γ1, by simpa [Category.assoc] using h2, inferInstance, ?_⟩
      intro x hx
      rw [pl_comp]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact k2
      · rw [k1 x hx, map_zero]
  have := Fintype.ofFinite (Ht q (sch.obj C) m i)
  obtain ⟨C', γ, h1, h2, h3⟩ := key Finset.univ
  exact ⟨C', γ, h1, h2, AddMonoidHom.ext fun x => by simpa using h3 x (Finset.mem_univ x)⟩

end LateralTheory.E.LeafKillCut

end
