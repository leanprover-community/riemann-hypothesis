module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC

theorem GlobalTheory.DefiniteBC.spehInf_map_sub_eq_sum_twists : ∀ (d : ℕ) (m : Multiset ℂ) (F : ℂ),
  ∑ k : Fin d, m.map (fun z => F + (((d : ℂ) - 1) / 2 - (k : ℕ)) - z) = (spehInf d m).map (fun z => F - z) := by
  intro d m F
  have hL : ∀ (f : ℕ → Multiset ℂ) (n : ℕ), ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => m.map (fun z => F + (((d : ℂ) - 1) / 2 - (k : ℕ)) - z)) d]
  unfold spehInf
  rw [hL]
  have hM := map_sum (Multiset.mapAddMonoidHom (fun z : ℂ => F - z))
    (fun k : ℕ => m.map (fun x => x + (((d : ℂ) - 1) / 2 - k))) (Finset.range d)
  simp only [Multiset.mapAddMonoidHom_apply] at hM
  rw [hM]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
