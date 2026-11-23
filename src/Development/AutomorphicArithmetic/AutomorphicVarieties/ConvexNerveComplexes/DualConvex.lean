module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.dual_convex : ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Y → E →L[ℝ] ℝ) (T : Set E), Convex ℝ (posDual T) ∧ ∀ h : E, IsClosed (normalCone q h) ∧ Convex ℝ (normalCone q h) := by
  intro E Y _ _ q T
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · intro x hx y hy a b ha hb hab
    simp only [posDual, Set.mem_setOf_eq] at hx hy ⊢
    intro k hk hk0
    have h1 := hx k hk hk0
    have h2 := hy k hk hk0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | ha'
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using h2
    · nlinarith [mul_pos ha' h1, mul_nonneg hb h2.le]
  · have e : normalCone q h = ⋂ h' ∈ poly q, {x : E →L[ℝ] ℝ | x h ≤ x h'} := by
      ext x
      simp [normalCone]
    rw [e]
    exact isClosed_biInter fun h' _ =>
      isClosed_le (ContinuousLinearMap.apply ℝ ℝ h).continuous (ContinuousLinearMap.apply ℝ ℝ h').continuous
  · intro x hx y hy a b ha hb hab
    simp only [normalCone, Set.mem_setOf_eq] at hx hy ⊢
    intro h' hh'
    have h1 := hx h' hh'
    have h2 := hy h' hh'
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
