module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

private theorem multiset_bind_pure_coe_eq_map (S : Multiset ℂˣ) :
    (do let a ← S; Pure.pure (a : ℂ) : Multiset ℂ) = Multiset.map (fun a : ℂˣ => (a : ℂ)) S := by
  show Multiset.bind S (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton _ _

private theorem multiset_map_fin_eq_map_range (t : ℕ) (f : ℕ → ℂ) :
    Multiset.map (fun i : Fin t => f i) Finset.univ.val = Multiset.map f (Finset.range t).val := by
  rw [Fin.univ_val_map, List.ofFn_eq_map]
  have h : List.map (fun i : Fin t => f i) (List.finRange t) = List.map f (List.range t) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [h, ← Multiset.map_coe]
  rfl

theorem UpperTheory.Gal.TP.Sub.satId_holds :
    SatId := by
  intro E _ _ w n t B x y k c hk hc
  have hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hs : ∀ m : ℕ, (((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ)) : ℂ) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) - 1) / 2) := by
    intro m
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  simp only [algSat, GlobalTheory.LFun.seg, hs]
  rw [multiset_bind_pure_coe_eq_map, multiset_bind_pure_coe_eq_map]
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  have hR := multiset_map_fin_eq_map_range t (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ)))
  have hc' : c = fun i : Fin t => (fun j : ℕ => (x : ℂ) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) + 2 * t - 2) / 2 - (j : ℂ))) (i : ℕ) := funext hc
  rw [hc', hR]
  congr 1
  · apply Multiset.map_congr rfl
    intro b _
    simp only [Function.comp, Units.val_mul, Units.val_inv_eq_inv_val, hk]
    have hsplit : (((n + t : ℕ) : ℂ) - 1) / 2 = ((n : ℂ) - 1) / 2 + (t : ℂ) / 2 := by
      push_cast
      ring
    rw [hsplit, Complex.cpow_add _ _ hq0, Complex.cpow_neg, mul_inv, mul_inv, inv_inv, inv_inv]
    ring
  · apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp, Units.val_mul, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
    rw [mul_left_comm, ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
