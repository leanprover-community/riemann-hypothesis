module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

section SDeg

variable {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A)

theorem sdegMul_zero : ∀ k : ℕ, SDegD d k (0 : A)
  | 0 => fun j => by simp
  | k + 1 => fun j => by simpa using sdegMul_zero k

theorem sdegMul_add : ∀ (k : ℕ) (a b : A), SDegD d k a → SDegD d k b → SDegD d k (a + b)
  | 0, a, b, ha, hb => fun j => by simp [map_add (f := _), ha j, hb j]
  | k + 1, a, b, ha, hb => fun j => by
    rw [map_add (f := _)]
    exact sdegMul_add k _ _ (ha j) (hb j)

theorem symbol_degree_mul : ∀ (n k l : ℕ) (f g : A), k + l = n → SDegD d k f → SDegD d l g → SDegD d n (f * g) := by
  intro n
  induction n with
  | zero =>
    intro k l f g hn hf hg
    obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := ⟨by omega, by omega⟩
    intro j
    simp only [Derivation.leibniz, hf j, hg j, smul_zero, add_zero]
  | succ n ih =>
    intro k l f g hn hf hg j
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    apply sdegMul_add
    · cases l with
      | zero => rw [show d j g = 0 from hg j, mul_zero]; exact sdegMul_zero d n
      | succ l => exact ih k l f (d j g) (by omega) hf (hg j)
    · cases k with
      | zero => rw [show d j f = 0 from hf j, mul_zero]; exact sdegMul_zero d n
      | succ k => exact ih l k g (d j f) (by omega) hg (hf j)

end SDeg

theorem pSDegMul : PSDegMul := by
  intro A _ ι d f g k l hf hg
  exact symbol_degree_mul d (k + l) k l f g rfl hf hg

end PI.EntAtD.W
