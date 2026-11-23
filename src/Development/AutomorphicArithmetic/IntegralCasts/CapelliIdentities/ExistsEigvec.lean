module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix IsLocalRing Polynomial

private theorem UpperTheory.Reformulated.B.Qf19.exists_eigvec {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R)
    (hu : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b))
    (hm : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R) (a : Fin 3) :
    ∃ (l : R) (v : Fin 3 → R), v a = 1 ∧ (∀ b, b ≠ a → v b ∈ maximalIdeal R) ∧ X *ᵥ v = l • v := by
  have hd : X.map (residue R) = diagonal fun b => residue R (X b b) := by
    ext b c
    by_cases h : b = c
    · subst h; simp
    · rw [diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]; exact hm b c h
  have hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0 := fun b hb => by
    rw [← map_sub]; exact ((hu a b hb.symm).map (residue R)).ne_zero
  have hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)
  have hc : X.charpoly.map (residue R) =
      (Polynomial.X - C (residue R (X a a))) *
        ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b))) := by
    rw [← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal,
      Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]
  obtain ⟨l, hl, hla⟩ := HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a)
    (by
      rw [← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]
      simp)
    (by
      change IsUnit (residue R _)
      rw [← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]
      simpa [eval_prod] using hP)
  have hla' : residue R l = residue R (X a a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hla
  set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM
  have hdet : M.det = 0 := by rw [hM, ← Matrix.eval_charpoly]; exact hl
  have hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b) := by
    ext b c
    have := congrFun (congrFun hd b) c
    by_cases h : b = c
    · subst h; simp [hM, hla']
    · rw [diagonal_apply_ne _ h] at this ⊢
      simpa [hM, diagonal_apply_ne _ h] using this
  have hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i,
      (residue R (X a a) - residue R (X j j))) b a := fun b => by
    have := (residue R).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal] at this
    exact congrFun (congrFun this b) a
  have hun : IsUnit (M.adjugate a a) := by
    rw [← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]; exact hP
  obtain ⟨u, hu'⟩ := hun
  have hker : M *ᵥ (fun b => M.adjugate b a) = 0 := by
    ext b
    have := congrFun (congrFun (mul_adjugate M) b) a
    rw [hdet, zero_smul] at this
    exact this
  refine ⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩
  · simp [← hu']
  · refine Ideal.mul_mem_left _ _ ?_
    rw [← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]
  · rw [hM, sub_mulVec, sub_eq_zero] at hker
    rw [mulVec_smul, ← hker, smul_comm l]
    congr 1
    ext b
    simp [mulVec_diagonal, hM]

theorem UpperTheory.Reformulated.B.Qf19.exists_canon :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (X : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
      (∀ (a b : Fin (3 : ℕ)), a ≠ b → IsUnit (X a a - X b b)) →
        (∀ (a b : Fin (3 : ℕ)), a ≠ b → X a b ∈ IsLocalRing.maximalIdeal R) →
          ∃ (h : GL (Fin (3 : ℕ)) R), UpperTheory.V.UnitaryThreeInertia.Canon X h := by
  intro R _ _ _ X hu hm
  choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm
  set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH
  have hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R := fun a b => by
    by_cases h : a = b
    · subst h; simp [hH, h1]
    · simpa [hH, one_apply_ne h] using h2 b a h
  have hmap : (residue R).mapMatrix H = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hhat a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, map_apply, this]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]
  have hdet : IsUnit H.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]; simp
  obtain ⟨h, hh⟩ := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hXH : X * H = H * diagonal l := by
    ext b a
    have := congrFun (h3 a) b
    rw [mul_diagonal, mul_comm]
    exact this
  refine ⟨h, ?_, fun a => ?_, ?_⟩
  · intro a b; rw [hh]; exact hhat a b
  · rw [hh]; exact h1 a
  · have : ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l := by
      rw [Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]
      simp
    rw [this]; exact isDiag_diagonal l
