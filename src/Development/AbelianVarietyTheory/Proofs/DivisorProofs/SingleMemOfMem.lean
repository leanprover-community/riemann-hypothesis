module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open scoped NNReal

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem smul_vec_apply {r : ℕ} (b : w.valuationSubring) (v : Fin r → C) (i : Fin r) :
    (b • v) i = (b : C) * v i := rfl

theorem smul_C (b : w.valuationSubring) (z : C) : b • z = (b : C) * z := rfl

theorem smul_pi_apply {S : Type} {r : ℕ} (b : w.valuationSubring) (x : S → Fin r → C) (s : S)
    (i : Fin r) : (b • x) s i = (b : C) * x s i := rfl

theorem exists_prod_apply {S : Type} [DecidableEq S] {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (x : S → Fin r → C) (hx : x ∈ Fil) (T : Finset S) :
    ∃ y ∈ Fil, ∀ s' i, y s' i = (∏ s ∈ T, ((a s' : C) - a s)) * x s' i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨x, hx, fun _ _ => by simp⟩
  | insert s0 T hs0 ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩
    rw [Finset.prod_insert hs0]
    simp only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]
    rw [smul_C, hyv]
    ring

theorem single_mem_of_mem {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}
    (a : S → w.valuationSubring) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (τ : S) (x : S → Fin r → C) (hx : x ∈ Fil) :
    (Pi.single τ (diffGen a τ • x τ) : S → Fin r → C) ∈ Fil := by
  obtain ⟨y, hy, hyv⟩ := exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)
  convert hy using 1
  funext s' i
  rw [hyv]
  by_cases e : s' = τ
  · subst e
    simp only [Pi.single_eq_same, smul_vec_apply, diffGen]
    push_cast
    rfl
  · rw [Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]
    simp [e]

theorem diffGen_ne_zero {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (τ : S) : diffGen a τ ≠ 0 := by
  rw [diffGen, Finset.prod_ne_zero_iff]
  intro s hs e
  exact (Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm

end GlobalTheory.Div.KerFil

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def clearDen {S : Type} [DecidableEq S] {r : ℕ}
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) : Submodule C (Fin r → C) where
  carrier := {v | ∃ b : w.valuationSubring, b ≠ 0 ∧ (Pi.single τ (b • v) : S → Fin r → C) ∈ Fil}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
    have : (Pi.single τ ((b * b') • (v + v')) : S → Fin r → C) =
        b' • (Pi.single τ (b • v) : S → Fin r → C) + b • (Pi.single τ (b' • v') : S → Fin r → C) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp only [Pi.single_eq_same, Pi.add_apply, smul_pi_apply, smul_vec_apply]
        push_cast; ring
      · simp [e]
    rw [this]
    exact add_mem (Fil.smul_mem _ h) (Fil.smul_mem _ h')
  smul_mem' := by
    rintro c v ⟨b, hb, h⟩
    by_cases hc0 : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc0]⟩
    rcases w.valuationSubring.mem_or_inv_mem c with hc | hc
    · refine ⟨b, hb, ?_⟩
      have : (Pi.single τ (b • c • v) : S → Fin r → C) =
          (⟨c, hc⟩ : w.valuationSubring) • (Pi.single τ (b • v) : S → Fin r → C) := by
        funext s i
        by_cases e : s = τ
        · subst e; simp only [Pi.single_eq_same, smul_pi_apply, smul_vec_apply, Pi.smul_apply,
            smul_eq_mul, smul_C]
          ring
        · simp [e]
      rw [this]
      exact Fil.smul_mem _ h
    · have hne : (⟨c⁻¹, hc⟩ : w.valuationSubring) ≠ 0 := by
        intro e
        exact hc0 (inv_eq_zero.1 (congrArg Subtype.val e))
      refine ⟨b * ⟨c⁻¹, hc⟩, mul_ne_zero hb hne, ?_⟩
      have : (b * ⟨c⁻¹, hc⟩ : w.valuationSubring) • c • v = b • v := by
        funext i
        simp only [smul_vec_apply, Pi.smul_apply, smul_eq_mul, smul_C]
        push_cast
        field_simp
      rw [this]
      exact h

end GlobalTheory.Div.KerFil
