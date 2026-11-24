module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Finset

namespace GlobalTheory.SignedHC.Model

theorem nMinus_parD (G : GridData) (i j : ℕ) : nMinus (G.parD i j) = (G.m - j) / 2 := by
  have : (G.parD i j).filter (fun x => x.2 = false) =
      (range ((G.m - j) / 2)).image fun a => (-(G.b (j + 2 + 2 * a) : ℚ), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parD, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨h | ⟨l, h1, h2, h3, h4⟩ | ⟨l, -, -, -, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · simp at h
      · have h5 : ¬ (l ≤ j + 1 ∨ Even (l - j - 1)) := by simpa using h4.symm
        rw [Nat.even_iff] at h5
        refine ⟨(l - j - 2) / 2, by omega, ?_, rfl⟩
        rw [show j + 2 + 2 * ((l - j - 2) / 2) = l by omega, h3]
      · simp at h
      · simp at h
    · rintro ⟨a, ha, rfl, rfl⟩
      refine ⟨Or.inr (Or.inl ⟨j + 2 + 2 * a, by omega, by omega, rfl, ?_⟩), rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro a ha a' ha' h
  simp only [coe_range, Set.mem_Iio] at ha ha'
  have h1 : G.b (j + 2 + 2 * a) = G.b (j + 2 + 2 * a') := by
    have := congrArg Prod.fst h
    simpa using this
  by_contra hne
  rcases lt_or_gt_of_ne hne with h2 | h2
  · have := G.b_mono (j + 2 + 2 * a) (j + 2 + 2 * a') (by omega) (by omega) (by omega); omega
  · have := G.b_mono (j + 2 + 2 * a') (j + 2 + 2 * a) (by omega) (by omega) (by omega); omega

end GlobalTheory.SignedHC.Model
