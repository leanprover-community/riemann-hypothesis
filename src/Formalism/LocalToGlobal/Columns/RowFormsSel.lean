module

public import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.EigenvalueLevelCeiling

section Sel

variable {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rf_tup_fin : (Qprime (mu : Chr X.F X.E X.K)).Finite :=
  auxiliary_primes_finite X.F X.E X.K _ ((mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2).1.2.1

theorem mem_QE (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ QE sel (mu : Chr X.F X.E X.K) ↔ ∃ v ∈ Qprime (mu : Chr X.F X.E X.K), sel v = P := by
  unfold QE
  rw [dite_eq_left (rf_tup_fin mu)]
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]

variable {sel}

end Sel

section Disj

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)


open Classical in
theorem QE_disj (hP : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : w ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hQ
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu w).mp hQ
  have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
    have key : ∀ i, sel v ∈ Pr.vG i → ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
      intro i hi
      have h0 : X.conjO (Pr.piG i) ≠ 0 := by
        intro h0
        have := hP.piG_norm i
        rw [h0, mul_zero] at this
        exact (Nat.cast_ne_zero.mpr (hP.g_prime i).ne_zero) this.symm
      rw [← hP.piG_norm i]
      exact Ideal.mul_mem_left _ _ ((mem_divs h0 _).mp hi)
    rcases Finset.mem_union.mp hw with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  obtain ⟨i, hi⟩ := hg
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hP.g_prime i)).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS i)

end Disj

end Formalism.L2.Col
