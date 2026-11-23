module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_v_le {c : L}
    (hc : ∀ m : ℕ, Valued.v c ≤ ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    c = 0 := by
  by_contra h0
  have hv : Valued.v c ≠ 0 := (_root_.map_ne_zero _).2 h0
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.1 hv
  have := hc (1 - Multiplicative.toAdd g).toNat
  rw [← hg, WithZero.coe_le_coe] at this
  have h2 : Multiplicative.toAdd g ≤ -(((1 - Multiplicative.toAdd g).toNat : ℕ) : ℤ) := by
    have := Multiplicative.toAdd_le.2 this
    simpa using this
  omega

theorem int_eq_zero_of_forall_dvd {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c : intL L}
    (hc : ∀ m : ℕ, piO h ^ m ∣ c) : c = 0 := by
  refine Subtype.ext (eq_zero_of_forall_v_le fun m => ?_)
  obtain ⟨d, hd⟩ := hc m
  have hd' : (c : L) = ϖ ^ m * (d : L) := by
    rw [hd]; simp
  have hdv : Valued.v (d : L) ≤ 1 := d.2
  rw [hd', map_mul, map_pow, h.2.2.2.1]
  calc ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * Valued.v (d : L)
      ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * 1 := by gcongr
    _ = _ := by
      rw [mul_one, ← WithZero.coe_pow, ← ofAdd_nsmul]
      congr 2
      simp

theorem eq_zero_of_forall_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) (ha : ∀ m, a ∈ piPow h P m) : a = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_dvd h fun m => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (ha m)
  refine ⟨(GlobalTheory.UTr.powBasis P).repr b i, ?_⟩
  have he : b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m =
      (piO h ^ m) • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  change b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m = a at hb
  rw [← hb, he, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem sep : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ)
    (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P),
    (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 :=
  fun _ _ _ _ _ _ h P a ha => eq_zero_of_forall_mem_piPow h P a ha

end GlobalTheory.NormEq
