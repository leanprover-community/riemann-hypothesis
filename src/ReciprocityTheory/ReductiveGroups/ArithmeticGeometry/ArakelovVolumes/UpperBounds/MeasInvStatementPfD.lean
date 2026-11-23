module

public import Mathlib.LinearAlgebra.Matrix.Block
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev UpI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // ¬ i.2.2 < i.2.1}

abbrev LoI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // i.2.2 < i.2.1}

def Umat (y : UpI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : ¬ b < a then y ⟨(τ, a, b), h⟩ else 0

lemma Umat_add (y y' : UpI ι r → ℂ) (τ : ι) : Umat (y + y') τ = Umat y τ + Umat y' τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma Umat_smul (c : ℂ) (y : UpI ι r → ℂ) (τ : ι) : Umat (c • y) τ = c • Umat y τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : (UpI ι r → ℂ) →ₗ[ℂ] (UpI ι r → ℂ) where
  toFun y i := (β i.1.1 * Umat y i.1.1) i.1.2.1 i.1.2.2
  map_add' y y' := by funext i; simp [Umat_add, Matrix.mul_add]
  map_smul' c y := by funext i; simp [Umat_smul]

def keyU (e : ι ≃ Fin (Fintype.card ι)) (i : UpI ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.1.2.2 : ℕ), toLex (r - (i.1.2.1 : ℕ), e i.1.1))

lemma keyU_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (keyU (r := r) e) := by
  rintro ⟨⟨τ, a, b⟩, hi⟩ ⟨⟨τ', a', b'⟩, hj⟩ h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨e.injective h3, Fin.ext ha, Fin.ext h1⟩

private lemma toMatrix_entry_lemma (β : ι → Matrix (Fin r) (Fin r) ℂ) (i j : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i j =
      if j.1.1 = i.1.1 ∧ j.1.2.2 = i.1.2.2 then β i.1.1 i.1.2.1 j.1.2.1 else 0 := by
  obtain ⟨⟨τ, a, b⟩, hi⟩ := i
  obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
  rw [LinearMap.toMatrix'_apply]
  simp only [Lβ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Umat, Matrix.of_apply]
  rw [Finset.sum_eq_single a']
  · by_cases h : τ' = τ ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hj, Pi.single_apply]
    · rw [if_neg h]
      split_ifs with h'
      · simp
      · rw [Pi.single_apply, if_neg, mul_zero]
        intro heq
        apply h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.2.symm⟩
  · intro c _ hc
    split_ifs with h'
    · simp
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact hc heq.2.1
  · simp

lemma toMatrix_Lβ_zero (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by
  rw [toMatrix_entry_lemma]
  split_ifs with h
  · obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
    obtain ⟨rfl, rfl⟩ := h
    simp only [keyU, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, and_false, or_false,
      true_and] at hij
    apply hβ _
    have := a.isLt; have := a'.isLt
    show (a' : ℕ) < a
    omega
  · rfl

lemma toMatrix_Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (i : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i i = β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [toMatrix_entry_lemma, if_pos ⟨rfl, rfl⟩]

theorem det_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [← LinearMap.det_toMatrix']
  let e := Fintype.equivFin ι
  letI : LinearOrder (UpI ι r) := LinearOrder.lift' (keyU (r := r) e) (keyU_injective e)
  have h := Matrix.det_of_lowerTriangular (LinearMap.toMatrix' (Lβ β)) (fun i j hij =>
    toMatrix_Lβ_zero e β hβ i j hij)
  convert h using 2 with i
  exact (toMatrix_Lβ_diag β hβ i).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
