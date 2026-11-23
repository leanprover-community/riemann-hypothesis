module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y : M4 R) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hX i k h, zero_mul]
    · rw [hY k i h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem up_adj {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := by
  intro i j h
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

theorem UpperTheory.V.Ws.Lab.upConj :
    ∀ (R : Type) [CommRing R] (b T : M4 R), IsGSp 1 b → IsUp b → IsUp T → IsUp (b * T * adj b) ∧ ∀ i, (b * T * adj b : M4 R) i i = T i i := by
  intro R _ b T hb hbu hT
  have hadj := up_adj hbu
  refine ⟨up_mul (up_mul hbu hT) hadj, fun i => ?_⟩
  have h1 : b i i * adj b i i = 1 := by
    have := congrFun (congrFun (sp_mul_adj hb) i) i
    rw [up_mul_diag hbu hadj] at this
    simpa using this
  rw [up_mul_diag (up_mul hbu hT) hadj, up_mul_diag hbu hT]
  linear_combination (T i i) * h1
