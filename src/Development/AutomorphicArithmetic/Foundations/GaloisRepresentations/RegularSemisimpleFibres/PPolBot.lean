module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open Polynomial

namespace UpperTheory.Gal.InertialTypesAlt

private theorem polBot_block (Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (c : ℕ → ℕ) (m : ℕ) :
    (((Multiset.range m).map fun j => ((1 : ℕ), ((c j : ℕ) : ZMod (Q - 1)))).map
      fun b => (X - C (x ^ b.2.val)) ^ b.1).prod = ∏ j ∈ Finset.range m, (X - C (x ^ c j)) := by
  haveI : NeZero (Q - 1) := ⟨by omega⟩
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.range_val]
  congr 1
  apply Multiset.map_congr rfl
  intro j _
  simp only [Function.comp, pow_one, ZMod.val_natCast]
  rw [← pow_eq_pow_mod _ hx]

private theorem polBot_list (q Q : ℕ) (x : ℂ) (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (L : List (ℕ × ℕ)) :
    (((L.map fun p => (Multiset.range p.1).map fun j =>
      ((1 : ℕ), ((p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)) : ℕ) : ZMod (Q - 1)))).sum).map
        fun b => (X - C (x ^ b.2.val)) ^ b.1).prod =
      (L.map fun p => ∏ j ∈ Finset.range p.1, (X - C (x ^ (p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1)))))).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, Multiset.map_add (f := _), Multiset.prod_add, ih, List.map_cons, List.prod_cons,
      polBot_block Q x hQ hx (fun j => p.2 * q ^ j * ((Q - 1) / (q ^ p.1 - 1))) p.1]

theorem polBot : PolBot := by
  intro q Q L x hQ hx
  have h := polBot_list q Q x hQ hx L
  simpa [Lbl.pol, Lbl.blocks] using h

end UpperTheory.Gal.InertialTypesAlt
