module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.FockCompare.WeylCreate

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

theorem killed_succ_iff (N : ℕ) (m : M) : Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨l', i, rfl⟩
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

theorem foldr_add_smul (l : List I) (β : ℂ) (x y : M) :
    l.foldr (fun i x => a i x) (x + β • y) =
      l.foldr (fun i x => a i x) x + β • l.foldr (fun i x => a i x) y := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_add (f := _), map_smul]

theorem foldr_zero (l : List I) : l.foldr (fun i x => a i x) (0 : M) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_zero]

theorem killed_create : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M),
    (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) →
    ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  intro I M _ _ a c hc N
  induction N with
  | zero =>
    intro m hm l _
    have h0 : m = 0 := hm [] rfl
    rw [h0, map_zero]
    exact foldr_zero l
  | succ N ih =>
    intro m hm
    rw [killed_succ_iff]
    intro i
    obtain ⟨β, hβ⟩ := hc i
    have e : a i (c m) = c (a i m) + β • m := by
      have := LinearMap.congr_fun hβ m
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      rw [← this]; abel
    have h1 := ih (a i m) ((killed_succ_iff N m).1 hm i)
    intro l hl
    rw [e, foldr_add_smul, h1 l hl, hm l hl, smul_zero, add_zero]

end GlobalTheory.FockCompare.WeylCreate
