module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma muSpan_base {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (R : Subalgebra ℂ S) (i j a : Fin (d + 1)) :
    InSp R (fun t => T.r n11 T.mu i j (dj j t)) (T.r n11 T.mu i j (toLex (a, j))) := by
  by_cases h : a = j
  · subst h
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    simp [Sys.r, Sys.mu, mul_comm]
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq h
    refine ⟨Pi.single t 1, fun l => ?_, ?_⟩
    · by_cases hl : l = t
      · subst hl
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hl] using R.zero_mem
    · rw [Finset.sum_eq_single t]
      · simp only [Pi.single_eq_same, one_mul]
        rfl
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro hb
        exact absurd (Finset.mem_univ t) hb

private lemma muSpan_rel {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (i j : Fin (d + 1)) (l : Mi d) :
    T.r n11 T.mu i j l =
      ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).1, j)) -
      ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).2, j)) := by
  have hv : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hu : ∀ l' : Mi d, T.u n11 i j l' = T.X i * T.Y j := fun _ => by simp [Sys.u, n11]
  simp only [Sys.r, Sys.mu, ofLex_toLex, Units.val_mul, hu]
  linear_combination (-((T.X (ofLex l).1 : S) * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1) *
    ((T.X i * T.Y j)⁻¹ : Sˣ)) * hv

theorem UpperTheory.Gal.productCup_of_system.muSpan_of :
    MuSpan := by
  intro d S E _ _ _ _ T hT I J i hi j hj l
  have hI : I.Nonempty := ⟨i, hi⟩
  obtain ⟨p, hp, hp'⟩ := muSpan_base T (T.R I J) i j (ofLex l).1
  obtain ⟨q, hq, hq'⟩ := muSpan_base T (T.R I J) i j (ofLex l).2
  have hb := hT.memY I J hI j hj (ofLex l).2
  have ha := hT.memY I J hI j hj (ofLex l).1
  refine ⟨fun t => ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * p t -
    ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * q t, fun t => ?_, ?_⟩
  · exact sub_mem (mul_mem hb (hp t)) (mul_mem ha (hq t))
  · rw [muSpan_rel T i j l, hp', hq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
