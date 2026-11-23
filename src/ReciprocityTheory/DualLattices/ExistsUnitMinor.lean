module

public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Valuation.Integers
import ReciprocityTheory.DualLattices.TensorSpan

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem freePts_integral {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) {w : Fin n × Fin h → C} (hw : w ∈ F.pts)
    (y : Fin n × Fin h) : v (w y) ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [hF]
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun x _ => ?_
  rw [map_mul]
  refine mul_le_one₀ ?_ (zero_le) (hc x)
  simp only [freeMat, Matrix.of_apply]
  split_ifs
  · rw [map_pow]
    exact pow_le_one₀ (zero_le) (ha _)
  · simp

def fder {n : ℕ} (a : Fin n → C) (τ : Fin n) : C := ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

theorem prod_fder {n : ℕ} (a : Fin n → C) : ∏ τ, fder a τ = discr a := rfl

private lemma valuation_coeff_prod_X_sub_C_le_one {n : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (s : Finset (Fin n)) (k : ℕ) :
    v ((∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))).coeff k) ≤ 1 := by
  have h : (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))) =
      (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (⟨a τ', ha τ'⟩ : v.integer))).map v.integer.subtype := by
    simp [Polynomial.map_prod]
  rw [h, Polynomial.coeff_map]
  exact (Valuation.mem_integer_iff _ _).1 (Subtype.prop _)

theorem conductor_mem {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) (τ : Fin n) (u : Fin h → C)
    (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => if y.1 = τ then fder a τ * u y.2 else 0) ∈ F.pts := by
  classical
  have hdeg : (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).natDegree < n := by
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_lt (Fin.pos τ) one_pos
  have heval : ∀ τ', (∏ τ'' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ''))).eval (a τ') =
      if τ' = τ then fder a τ else 0 := by
    intro τ'
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs with h
    · subst h
      rfl
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)
  refine ⟨fun x => (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff x.1 * u x.2,
    fun x => ?_, ?_⟩
  · rw [map_mul]
    exact mul_le_one₀ (valuation_coeff_prod_X_sub_C_le_one ha _ _) (zero_le) (hu _)
  · rw [hF]
    funext y
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, freeMat, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsum : ∑ k : Fin n, a y.1 ^ (k : ℕ) *
        ((∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff k * u y.2) =
        (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).eval (a y.1) * u y.2 := by
      rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul,
        ← Fin.sum_univ_eq_sum_range (fun i => _ * a y.1 ^ i * u y.2)]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, heval]
    split_ifs <;> simp

end ReciprocityTheory.PGsh.Up
