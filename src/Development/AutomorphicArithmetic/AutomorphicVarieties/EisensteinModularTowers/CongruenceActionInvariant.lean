module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.congruence_action_invariant :
    ∀ (l : ℕ) [Fact l.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ (z : (ZMod (l ^ L))ˣ) (t : SL(2, ZMod (l ^ L)) → (ZMod (l ^ L))ˣ → GL (Fin 2) (ZMod (l ^ L))), (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = h i 0) → (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = (u : ZMod (l ^ L)) * h i 1) → ∀ (V : Type) [AddCommMonoid V] (f : GL (Fin 2) (ZMod (l ^ L)) → V), ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ L)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ L))ˣ => (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m]), f (t h (a * z)) = ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ L)).val : ℕ) : ZMod (l ^ m))), f γ := by
  intro l _ L m _ hmL z t ht0 ht1 V _ f
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  set φ := ZMod.castHom hd (ZMod (l ^ m)) with hφ
  have hcast : ∀ x : ZMod (l ^ L), ((x.val : ℕ) : ZMod (l ^ m)) = φ x := by
    intro x
    rw [ZMod.natCast_val, hφ, ZMod.castHom_apply]
  have hmod : ∀ a : (ZMod (l ^ L))ˣ, (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m] ↔ φ a = 1 := by
    intro a
    rw [← ZMod.natCast_eq_natCast_iff, hcast, Nat.cast_one]
  have hdet : ∀ h u, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det
      = (u : ZMod (l ^ L)) := by
    intro h u
    have h1 : (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = 1 := h.prop
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [ht0, ht0, ht1, ht1]
    linear_combination (u : ZMod (l ^ L)) * h1
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => t p.1 (p.2 * z))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, ht0, hcast, hdet]
    refine ⟨hp.1, ?_⟩
    rw [Units.val_mul, map_mul, (hmod _).mp hp.2, one_mul]
  · intro p _ q _ hpq
    have hu : p.2 * z = q.2 * z := by
      apply Units.ext
      rw [← hdet p.1, ← hdet q.1, hpq]
    have ha : p.2 = q.2 := mul_right_cancel hu
    have hh : p.1 = q.1 := by
      ext i j
      fin_cases j
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0) hpq
        simpa [ht0] using this
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1) hpq
        simp only [ht1] at this
        rw [hu] at this
        exact (Units.mul_right_inj _).mp this
    exact Prod.ext hh ha
  · intro γ hγ
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, hcast] at hγ
    set g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) with hg
    set u : (ZMod (l ^ L))ˣ := Matrix.GeneralLinearGroup.det γ with hu
    have hug : (u : ZMod (l ^ L)) = g.det := rfl
    set M : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) :=
      !![g 0 0, (↑u⁻¹ : ZMod (l ^ L)) * g 0 1; g 1 0, (↑u⁻¹ : ZMod (l ^ L)) * g 1 1] with hM
    have hMdet : M.det = 1 := by
      rw [hM, Matrix.det_fin_two_of]
      have h2 : (↑u⁻¹ : ZMod (l ^ L)) * g.det = 1 := by
        rw [← hug, Units.inv_mul]
      rw [Matrix.det_fin_two] at h2
      linear_combination h2
    refine ⟨(⟨M, hMdet⟩, u * z⁻¹), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hγ.1⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmod, Units.val_mul, map_mul, hug, hγ.2, ← map_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, map_one]
    · apply Units.ext
      have hz : u * z⁻¹ * z = u := by group
      have e0 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = g i 0 := by
        intro i
        refine (ht0 _ _ i).trans ?_
        fin_cases i <;> rfl
      have e1 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = g i 1 := by
        intro i
        refine (ht1 _ _ i).trans ?_
        rw [hz]
        fin_cases i
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 0 1) = g 0 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 1 1) = g 1 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
      ext i j
      fin_cases j
      · exact e0 i
      · exact e1 i
  · intro p _
    rfl
