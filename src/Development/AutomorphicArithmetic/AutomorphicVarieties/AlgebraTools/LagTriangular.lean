module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
public import Mathlib.RingTheory.Idempotents
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem left_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ f * x = u • f) :
    ∃ u : R, IsUnit u ∧ f * L.prod = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨u * v, hu.mul hv, by
      rw [List.prod_cons, ← mul_assoc, e, smul_mul_assoc, e', smul_smul]⟩

private theorem right_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ x * f = u • f) :
    ∃ u : R, IsUnit u ∧ L.prod * f = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨v * u, hv.mul hu, by
      rw [List.prod_cons, mul_assoc, e', mul_smul_comm, e, smul_smul]⟩

private theorem mid_zero {R E : Type} [CommRing R] [Ring E] [Algebra R E] {n : ℕ} (f g : E)
    (F : Fin n → E) (i : Fin n)
    (hf : ∀ j, j < i → ∃ u : R, IsUnit u ∧ f * F j = u • f)
    (hg : ∀ j, i < j → ∃ u : R, IsUnit u ∧ F j * g = u • g)
    (h0 : (List.ofFn F).prod = 0) : f * F i * g = 0 := by
  have hlen : (List.ofFn F).length = n := List.length_ofFn
  have hsplit : List.ofFn F = (List.ofFn F).take i ++ F i :: (List.ofFn F).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn F)]
    congr 1
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact i.2)]
    simp
  have hT : ∀ x ∈ (List.ofFn F).take i, ∃ u : R, IsUnit u ∧ f * x = u • f := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, hlen] at hk
    rw [List.getElem_take, List.getElem_ofFn]
    exact hf ⟨k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  have hD : ∀ x ∈ (List.ofFn F).drop (i + 1), ∃ u : R, IsUnit u ∧ x * g = u • g := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_drop, hlen] at hk
    rw [List.getElem_drop, List.getElem_ofFn]
    exact hg ⟨i + 1 + k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  obtain ⟨u, hu, hA⟩ := left_unit (R := R) f _ hT
  obtain ⟨v, hv, hB⟩ := right_unit (R := R) g _ hD
  have key : f * (List.ofFn F).prod * g = (u * v) • (f * F i * g) := by
    rw [hsplit, List.prod_append, List.prod_cons]
    calc f * (((List.ofFn F).take i).prod * (F i * ((List.ofFn F).drop (i + 1)).prod)) * g
        = (f * ((List.ofFn F).take i).prod) * F i * (((List.ofFn F).drop (i + 1)).prod * g) := by
          simp only [mul_assoc]
      _ = (u • f) * F i * (v • g) := by rw [hA, hB]
      _ = (u * v) • (f * F i * g) := by
          rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h0, mul_zero, zero_mul] at key
  exact ((hu.mul hv).smul_eq_zero).1 key.symm

theorem UpperTheory.V.AlgebraTools.lag_triangular :
    ∀ {R Λ E : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Ring E] [Algebra R E] {n : ℕ} (ρ : Λ →ₐ[R] E) (χ : Fin n → Λ →ₐ[R] R) (z : Λ), (∀ y : Fin n → Λ, (List.ofFn fun i => ρ (y i) - algebraMap R E (χ i (y i))).prod = 0) → (∀ i j, i ≠ j → IsUnit (χ i z - χ j z)) → CompleteOrthogonalIdempotents (lag (fun i => χ i z) (ρ z)) ∧ (∀ (y : Λ) (a b : Fin n), b < a → lag (fun i => χ i z) (ρ z) a * ρ y * lag (fun i => χ i z) (ρ z) b = 0) ∧ ∀ (y : Λ) (i : Fin n), lag (fun i => χ i z) (ρ z) i * ρ y * lag (fun i => χ i z) (ρ z) i = χ i y • lag (fun i => χ i z) (ρ z) i := by
  intro R Λ E _ _ _ _ _ n ρ χ z hprod hu
  have hzero : aeval (ρ z) (∏ i, (X - C ((fun i => χ i z) i))) = 0 := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simpa [Function.comp_def] using hprod (fun _ => z)
  obtain ⟨hcoi, hP, -, hcomm⟩ := lag_coi (fun i => χ i z) (ρ z) hu hzero
  have hl : ∀ c j, lag (fun i => χ i z) (ρ z) c * (ρ z - algebraMap R E (χ j z)) =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [mul_sub, ← (hcomm (ρ z) c (Commute.refl _)).eq, hP, ← Algebra.commutes,
      ← Algebra.smul_def, sub_smul]
  have hr : ∀ c j, (ρ z - algebraMap R E (χ j z)) * lag (fun i => χ i z) (ρ z) c =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [sub_mul, hP, ← Algebra.smul_def, sub_smul]
  have key : ∀ (y : Λ) (c d i : Fin n), (∀ j, j < i → j ≠ c) → (∀ j, i < j → j ≠ d) →
      lag (fun i => χ i z) (ρ z) c * (ρ y - algebraMap R E (χ i y)) *
        lag (fun i => χ i z) (ρ z) d = 0 := by
    intro y c d i h1 h2
    have h := mid_zero (R := R) (lag (fun i => χ i z) (ρ z) c) (lag (fun i => χ i z) (ρ z) d)
      (fun j => ρ (Function.update (fun _ => z) i y j) -
        algebraMap R E (χ j (Function.update (fun _ => z) i y j))) i ?_ ?_ (hprod _)
    · simpa using h
    · intro j hj
      refine ⟨_, hu c j (h1 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_lt hj)]
      exact hl c j
    · intro j hj
      refine ⟨_, hu d j (h2 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_gt hj)]
      exact hr d j
  have hmid : ∀ (r : R) (c d : Fin n), lag (fun i => χ i z) (ρ z) c * algebraMap R E r *
      lag (fun i => χ i z) (ρ z) d =
        r • (lag (fun i => χ i z) (ρ z) c * lag (fun i => χ i z) (ρ z) d) := by
    intro r c d
    rw [← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc]
  refine ⟨hcoi, ?_, ?_⟩
  · intro y a b hba
    have h := key y a b a (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt (hba.trans hj))
    rw [mul_sub, sub_mul, hmid, hcoi.ortho (ne_of_gt hba), smul_zero, sub_zero] at h
    exact h
  · intro y i
    have h := key y i i i (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt hj)
    rw [mul_sub, sub_mul, hmid, (hcoi.idem i).eq, sub_eq_zero] at h
    exact h
