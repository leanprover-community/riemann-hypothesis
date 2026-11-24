module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ) [Fact l.Prime], (∀ k : ℕ, InZl ε l n (k : Ω)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F + G)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F * G)) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (k : ℕ), s (zt ε l n) = zt ε l n ^ k → ∀ F : Ω, InZl ε l n F → InZl ε l n (s F) := by
  intro Ω _ _ ε l n hl
  have hp : l.Prime := hl.out
  have hmul : ∀ D E : ℕ, ¬ l ∣ D → ¬ l ∣ E → ¬ l ∣ D * E := fun D E hD hE h =>
    ((Nat.Prime.dvd_mul hp).1 h).elim hD hE
  refine ⟨fun k => ⟨1, hp.not_dvd_one, ?_⟩, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, one_mul]
    exact natCast_mem _ k
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F + G) = (E : Ω) * ((D : Ω) * F) + (D : Ω) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact add_mem (mul_mem (natCast_mem _ E) hF) (mul_mem (natCast_mem _ D) hG)
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F * G) = ((D : Ω) * F) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact mul_mem hF hG
  · rintro s k hs F ⟨D, hD, hF⟩
    refine ⟨D, hD, ?_⟩
    have key : ∀ y ∈ Subring.closure ({zt ε l n} : Set Ω), s y ∈ Subring.closure ({zt ε l n} : Set Ω) := by
      intro y hy
      have hle : Subring.closure ({zt ε l n} : Set Ω) ≤
          (Subring.closure ({zt ε l n} : Set Ω)).comap (s : Ω →+* Ω) := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        show s (zt ε l n) ∈ Subring.closure ({zt ε l n} : Set Ω)
        rw [hs]
        exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) k
      exact hle hy
    have h := key _ hF
    rwa [map_mul, map_natCast] at h
