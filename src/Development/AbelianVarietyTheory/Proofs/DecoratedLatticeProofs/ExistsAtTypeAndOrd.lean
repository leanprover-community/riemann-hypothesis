module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.AtTypeExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section Compl
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, e⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
    have h2 := congrArg (P.valuation E) e
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one P r
  · intro h
    obtain ⟨r, s, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a h
    exact ⟨r, s.1, s.2, by rw [mul_comm]; exact e⟩

theorem valuation_norm (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    P.valuation E ((qOf P : ℕ) : E) = WithZero.exp (-1 : ℤ) := by
  have hm : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E) := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 1).2 (by simpa using hm)
  have h2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 2).1 h
  have h0 : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

end Compl

theorem exists_ord : (∀ κ τ j : ℕ, ∃ e : XIx (Fin κ) (Fin τ) j ≃ Fin (κ + j * (τ + 1)), IsOrd xPos e) ∧ (∀ κ τ l j : ℕ, ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ), IsOrd zPos e) ∧ (∀ (A : Type) (n c : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → ∃ e : A ⊕ Fin c ≃ Fin (n + c), IsOrd (yPos pos n) e) ∧ (∀ (A : Type) (n N : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → N = n + 1 → ∃ e : A ⊕ Unit ≃ Fin N, IsOrd (Sum.elim pos fun _ => N - 1) e) := by
  refine ⟨fun κ τ j => ?_, fun κ τ l j => ?_, fun A n c pos d hd => ?_, fun A n N pos d hd hN => ?_⟩
  · refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr (by ring)), ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [xPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv, ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [zPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr d (Equiv.refl _)).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa [yPos] using hd i
    · simp [yPos]
  · subst hN
    refine ⟨(Equiv.sumCongr d (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa using hd i
    · simp

end GlobalTheory.AtTypeExists
