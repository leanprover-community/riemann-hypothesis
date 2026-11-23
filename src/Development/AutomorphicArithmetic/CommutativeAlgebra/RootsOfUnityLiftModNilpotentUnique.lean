module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs
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
public import Mathlib.Dynamics.Newton
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

noncomputable section
open IsLocalRing UpperTheory.Et

private theorem isUnit_aeval_derivative {S : Type} [CommRing S] {q : ℕ} (hq : IsUnit (q : S)) (hq0 : q ≠ 0)
    {x : S} (hx : IsNilpotent (x ^ q - 1)) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))) := by
  have hxq : IsUnit (x ^ q) := by
    have h := IsNilpotent.isUnit_add_one hx
    simpa using h
  have hxu : IsUnit x := (isUnit_pow_iff hq0).1 hxq
  have h2 : Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))
      = (q : S) * x ^ (q - 1) := by
    simp [Polynomial.derivative_X_pow]
  rw [h2]
  exact hq.mul (hxu.pow _)

theorem UpperTheory.roots_of_unity_lift_mod_nilpotent_unique :
    ∀ (S : Type) [CommRing S] (q : ℕ), IsUnit (q : S) → (∀ x : S, IsNilpotent (x ^ q - 1) → ∃ y : S, y ^ q = 1 ∧ IsNilpotent (x - y)) ∧
      ∀ x y : S, x ^ q = 1 → y ^ q = 1 → IsNilpotent (x - y) → x = y := by
  intro S _ q hq
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : S) = 1 := by simpa using hq
    have : Subsingleton S := subsingleton_of_zero_eq_one h01
    exact ⟨fun x _ => ⟨x, Subsingleton.elim _ _, by simp⟩, fun x y _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx)
      (isUnit_aeval_derivative hq hq0 hx)
    refine ⟨y, ?_, hy1⟩
    simpa [sub_eq_zero] using hy2
  · have hx' : IsNilpotent (x ^ q - 1) := by simp [hx]
    have h := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx')
      (isUnit_aeval_derivative hq hq0 hx')
    exact h.unique ⟨by simp, by simp [hx]⟩ ⟨hxy, by simp [hy]⟩

end
