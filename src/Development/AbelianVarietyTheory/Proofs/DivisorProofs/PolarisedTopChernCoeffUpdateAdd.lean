module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem mixTop_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  intro n r _ _ K j L L'
  have key : ∀ (M : EndValuedForm11Coeffs n r) (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      (Matrix.of fun i b => Function.update K j M i (u i) b (p i) (p (π i))) =
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).updateRow j
          (fun b => M (u j) b (p j) (p (π j))) := by
    intro M p π u
    ext i b
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  unfold mixTop
  rw [← mul_add]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun u _ => ?_
  rw [key, key, key, ← mul_add, ← Matrix.det_updateRow_add]
  rfl

end GlobalTheory.GoodTop
