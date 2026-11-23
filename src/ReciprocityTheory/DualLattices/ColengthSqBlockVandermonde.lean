module

public import ReciprocityTheory.DualLattices.DiscriminantColengthStatement
public import Mathlib.LinearAlgebra.Vandermonde
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.DualLattices.TensorSpan

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def sumLat {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) :=
  ⟨Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B), by
    rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Mτ τ).det_ne⟩

lemma sumLat_apply {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (x y : Fin n × Fin s) :
    (sumLat Mτ).B x y = if x.1 = y.1 then (Mτ x.1).B x.2 y.2 else 0 := by
  simp only [sumLat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply]

lemma sumLat_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (c : Fin n × Fin s → C) (τ : Fin n)
    (i : Fin s) : ((sumLat Mτ).B *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
  simp only [Matrix.mulVec, dotProduct, sumLat_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun j _ => if_neg (Ne.symm hb)
  · intro h; exact absurd (Finset.mem_univ τ) h

lemma sumLat_pts {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : (sumLat Mτ).pts = sumPts Mτ := by
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
    funext i
    exact sumLat_mulVec Mτ c τ i
  · intro hw
    choose c hc hwc using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext ⟨τ, i⟩
    rw [sumLat_mulVec]
    exact congrFun (hwc τ) i

lemma freeMat_eq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [freeMat, Matrix.of_apply, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]

lemma det_freeMat {n : ℕ} (a : Fin n → C) (s : ℕ) :
    (freeMat a s).det = (Matrix.vandermonde a).det ^ s := by
  rw [freeMat_eq, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma v_det_vandermonde_sq {n : ℕ} (a : Fin n → C) :
    v (Matrix.vandermonde a).det ^ 2 = v (discr a) := by
  have hsplit : ∀ τ : Fin n, Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
    intro τ
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  have hdisj : ∀ τ : Fin n, Disjoint (Finset.Ioi τ) (Finset.Iio τ) := by
    intro τ
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Finset.mem_Ioi.1 h1) (Finset.mem_Iio.1 h2)
  rw [Matrix.det_vandermonde, discr]
  simp only [map_prod]
  have h1 : ∏ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
      (∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ')) *
        ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => by rw [hsplit τ, Finset.prod_union (hdisj τ)]
  have h2 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') =
      ∏ τ' : Fin n, ∏ τ ∈ Finset.Ioi τ', v (a τ - a τ') :=
    Finset.prod_comm' (by intro x y; simp [Finset.mem_Iio, Finset.mem_Ioi])
  have h3 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ') =
      ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ) :=
    Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => Valuation.map_sub_swap v _ _
  rw [h1, h2, h3, sq]

lemma v_det_freeMat_sq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    v (freeMat a s).det ^ 2 = v (discr a) ^ s := by
  rw [det_freeMat, map_pow, pow_right_comm, v_det_vandermonde_sq]

end ReciprocityTheory.PGsh.Up
