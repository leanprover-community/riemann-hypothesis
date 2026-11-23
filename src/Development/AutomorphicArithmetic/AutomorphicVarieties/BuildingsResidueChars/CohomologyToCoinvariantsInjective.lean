module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped Matrix

theorem UpperTheory.cohomology_to_coinvariants_injective :
    UpperTheory.V.Af.CohB.ToCoInj := by
  intro Γ X Y _ _ _ p hp y horb d ξ f f' h
  funext x
  obtain ⟨g, hg⟩ := horb x
  have hx : g • x ∈ UpperTheory.V.Af.CohB.fib p hp y := by
    change p (g • x) = y
    rw [hp, hg]
  have h1 : (UpperTheory.V.Af.CohB.toCo p hp y ξ f).1 g ⟨g • x, hx⟩
      = (UpperTheory.V.Af.CohB.toCo p hp y ξ f').1 g ⟨g • x, hx⟩ := by rw [h]
  rw [UpperTheory.V.Af.CohB.toCo_apply, UpperTheory.V.Af.CohB.toCo_apply] at h1
  simp only [inv_smul_smul] at h1
  have h2 := congrArg (fun v => ξ g⁻¹ *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
  exact h2
