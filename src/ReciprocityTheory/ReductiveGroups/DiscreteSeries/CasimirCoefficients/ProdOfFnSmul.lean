module

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBInvar
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}

lemma prod_ofFn_sum {α : Type*} [Fintype α] : ∀ {p : ℕ} (f : Fin p → α → 𝒰),
    (List.ofFn fun j => ∑ a, f j a).prod = ∑ γ : Fin p → α, (List.ofFn fun j => f j (γ j)).prod
  | 0, f => by simp
  | p + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_sum (fun j => f j.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (p + 1) => α).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun γ _ => ?_
    show _ = (List.ofFn fun j => f j (Fin.cons (α := fun _ => α) a γ j)).prod
    simp only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

lemma prod_ofFn_smul : ∀ {p : ℕ} (s : Fin p → ℂ) (a : Fin p → 𝒰),
    (List.ofFn fun j => s j • a j).prod = (∏ j, s j) • (List.ofFn a).prod
  | 0, s, a => by simp
  | p + 1, s, a => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [prod_ofFn_smul (fun j => s j.succ) (fun j => a j.succ), Fin.prod_univ_succ, smul_mul_smul_comm]

lemma capEntry_ad (E : Fin n → Fin n → 𝒰) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ)
    (a b : Fin n) :
    capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x a b =
      ∑ c, ∑ d, (P c a * Q b d) • capEntry E x c d := by
  simp only [capEntry, smul_add, Finset.sum_add_distrib]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_smul]
  have h : ∑ c, P c a * Q b c = (Q * P) b a := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [h, hQP, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab, zero_smul]

lemma coef_det (P : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • ∏ j, P (c j) (σ j) = (P.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Units.smul_def]
  rfl

lemma sum_fun_perm {M : Type*} [AddCommMonoid M] (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) : ∑ c, f c = ∑ τ : Equiv.Perm (Fin n), f τ := by
  apply PositivityTheory.Rg.Sw.WR.K.GB.Inv.sum_perm_of_noninj <;> assumption

theorem capelliC_ad (E : Fin n → Fin n → 𝒰) (hE : GlRelR E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (x : ℂ) :
    capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x = capelliC E x := by
  classical
  have hstep : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun j : Fin n =>
        capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j).prod =
        ∑ γ : Fin n → Fin n × Fin n, (∏ j, (P (γ j).1 (σ j) * Q j (γ j).2)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
    intro σ
    have h1 : ∀ j : Fin n, capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) (x - ((j : ℕ) : ℂ)) (σ j) j =
        ∑ cd : Fin n × Fin n, (P cd.1 (σ j) * Q j cd.2) • capEntry E (x - ((j : ℕ) : ℂ)) cd.1 cd.2 := by
      intro j
      rw [capEntry_ad E P Q hQP, Fintype.sum_prod_type]
    simp_rw [h1]
    rw [prod_ofFn_sum]
    exact Finset.sum_congr rfl (fun γ _ => prod_ofFn_smul _ _)
  have hdet : ∀ c : Fin n → Fin n, ¬ Function.Injective c → (P.submatrix c id).det = 0 := by
    intro c hc
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hc (fun i j hij => h i j hij)
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  have hS : ∀ d : Fin n → Fin n,
      ∑ c : Fin n → Fin n, (P.submatrix c id).det •
        (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod =
        P.det • cminor E id d x := by
    intro d
    rw [sum_fun_perm _ (fun c hc => by rw [hdet c hc, zero_smul])]
    unfold cminor
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Matrix.det_permute, mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul ℂ]
    simp only [id]
  have hQ : ∑ ρ : Equiv.Perm (Fin n), ((Equiv.Perm.sign ρ : ℤˣ) : ℤ) • ∏ j, Q j (ρ j) = Q.det := by
    have := coef_det Q id
    simpa using this
  calc capelliC (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x
      = ∑ γ : Fin n → Fin n × Fin n,
          ((P.submatrix (fun j => (γ j).1) id).det * ∏ j, Q j (γ j).2) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (γ j).1 (γ j).2).prod := by
        unfold capelliC cminor
        simp only [id]
        simp_rw [hstep, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        rw [← coef_det P (fun j => (γ j).1), Finset.sum_mul, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.prod_mul_distrib, smul_mul_assoc, smul_assoc]
    _ = ∑ d : Fin n → Fin n, ∑ c : Fin n → Fin n,
          ((P.submatrix c id).det * ∏ j, Q j (d j)) •
          (List.ofFn fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (c j) (d j)).prod := by
        let e : (Fin n → Fin n) × (Fin n → Fin n) ≃ (Fin n → Fin n × Fin n) :=
          ⟨fun cd j => (cd.1 j, cd.2 j), fun γ => (fun j => (γ j).1, fun j => (γ j).2),
            fun _ => rfl, fun _ => rfl⟩
        rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
        rfl
    _ = ∑ d : Fin n → Fin n, (∏ j, Q j (d j)) • (P.det • cminor E id d x) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← hS d, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [smul_smul, mul_comm]
    _ = ∑ ρ : Equiv.Perm (Fin n), (∏ j, Q j (ρ j)) • (P.det • cminor E id ρ x) := by
        apply sum_fun_perm
        intro d hd
        rw [cminor_cols_not_inj E hE id d x hd, smul_zero, smul_zero]
    _ = (P.det * Q.det) • capelliC E x := by
        rw [← hQ, Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun ρ _ => ?_)
        have hc := cminor_perm_cols E hE id id ρ x
        unfold capelliC
        rw [show (id : Fin n → Fin n) ∘ ρ = ρ from rfl] at hc
        rw [hc, smul_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        congr 1
        rw [zsmul_eq_mul]
        ring
    _ = capelliC E x := by
        rw [← Matrix.det_mul, hPQ, Matrix.det_one, one_smul]

end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
