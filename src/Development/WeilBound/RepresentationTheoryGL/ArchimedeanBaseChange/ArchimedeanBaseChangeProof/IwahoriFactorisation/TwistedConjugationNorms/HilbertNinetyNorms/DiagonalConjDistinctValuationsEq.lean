module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

namespace Rig

theorem diag_comm_entry {L : Type*} [CommRing L] {n : ℕ} (D D' H : Matrix (Fin n) (Fin n) L)
    (hD : ∀ i j, i ≠ j → D i j = 0) (hD' : ∀ i j, i ≠ j → D' i j = 0) (hc : D * H = H * D') (i j : Fin n) :
    D i i * H i j = H i j * D' j j := by
  have h := congrFun (congrFun hc i) j
  simp only [Matrix.mul_apply] at h
  rwa [Finset.sum_eq_single i (fun k _ hk => by rw [hD i k (Ne.symm hk), zero_mul]) (by simp),
    Finset.sum_eq_single j (fun k _ hk => by rw [hD' k j hk, mul_zero]) (by simp)] at h

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


end Rig

open Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem diagonal_conj_distinct_valuations_eq (w : Pl E) (n : ℕ) (v : Fin n → ℤ) (hv : Function.Injective v) (d d' h : GLw n w)
    (hd : (∀ i j : Fin n, i ≠ j → d.val i j = 0) ∧ ∀ i, ordL (d.val i i) = v i)
    (hd' : (∀ i j : Fin n, i ≠ j → d'.val i j = 0) ∧ ∀ i, ordL (d'.val i i) = v i)
    (hh : h⁻¹ * d * h = d') : d = d' ∧ ∀ i j : Fin n, i ≠ j → h.val i j = 0 := by
  obtain ⟨hd0, hdv⟩ := hd
  obtain ⟨hd'0, hd'v⟩ := hd'
  have hc : d.val * h.val = h.val * d'.val := by
    have hm : d * h = h * d' := by rw [← hh]; group
    simpa using congrArg Units.val hm
  have he := diag_comm_entry d.val d'.val h.val hd0 hd'0 hc
  have hoff : ∀ i j : Fin n, i ≠ j → h.val i j = 0 := by
    intro i j hij
    by_contra hne
    have hq : d.val i i = d'.val j j := mul_right_cancel₀ hne (by rw [he i j]; ring)
    apply hij
    apply hv
    rw [← hdv i, ← hd'v j, hq]
  have hdiag : ∀ i, h.val i i ≠ 0 := by
    intro i h0
    have h1 : (h.val * h⁻¹.val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [hoff i k hk, zero_mul]
  have hval : d.val = d'.val := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      have hq : d.val i i * h.val i i = d'.val i i * h.val i i := by rw [he i i]; ring
      exact mul_right_cancel₀ (hdiag i) hq
    · rw [hd0 i j hij, hd'0 i j hij]
  exact ⟨Units.ext hval, hoff⟩

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
