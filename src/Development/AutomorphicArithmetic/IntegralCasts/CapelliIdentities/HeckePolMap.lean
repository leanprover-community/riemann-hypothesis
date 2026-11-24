module

public import Mathlib.Algebra.Polynomial.Eval.Defs
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

noncomputable def UpperTheory.Reformulated.B.Qk6.heckePol :
    {A : Type} → [inst : CommRing A] → ℕ → ℕ → (ℕ → A) → Polynomial A :=
    fun {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) ↦
      ∑ j ∈ Finset.range (n + (1 : ℕ)),
        (Polynomial.C : A → Polynomial A) ((-1 : A) ^ j * (↑q : A) ^ (j * (j - (1 : ℕ)) / (2 : ℕ)) * a j) *
          Polynomial.X ^ (n - j)

theorem UpperTheory.Reformulated.B.Qk6.heckePol_map :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A),
      Polynomial.map f (UpperTheory.Reformulated.B.Qk6.heckePol n q a) = UpperTheory.Reformulated.B.Qk6.heckePol n q fun (j : ℕ) ↦ (f : A → B) (a j) := by
  intro A B _ _ f n q a
  unfold UpperTheory.Reformulated.B.Qk6.heckePol

  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    map_mul f, map_mul f, map_pow f, map_pow f, map_neg f, map_one f, map_natCast f]
