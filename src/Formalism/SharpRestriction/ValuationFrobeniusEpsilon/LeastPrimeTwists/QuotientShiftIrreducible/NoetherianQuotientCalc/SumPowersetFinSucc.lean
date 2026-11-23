module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open Finset

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem sum_powerset_fin_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ I ∈ (univ : Finset (Fin (n + 1))).powerset, f I =
      ∑ J ∈ (univ : Finset (Fin n)).powerset, f (J.image Fin.succ) +
        ∑ J ∈ (univ : Finset (Fin n)).powerset, f (insert 0 (J.image Fin.succ)) := by
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 ((univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j => Fin.succ_ne_zero j
  have hinj : Function.Injective (fun J : Finset (Fin n) => J.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective n)
  rw [hu, Finset.sum_powerset_insert h0, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]

end Formalism.MainNotions.V.Pf.V2.Calc
