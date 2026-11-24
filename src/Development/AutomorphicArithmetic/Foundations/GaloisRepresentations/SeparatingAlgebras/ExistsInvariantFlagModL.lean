module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module

namespace UpperTheory.Gal.Gen

private theorem exists_invariant_flag_mod_l (hF : FixVec) (l : ℕ) [Fact l.Prime] (H : Type) [Group H] (hH : IsPGroup l H)
    (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V] (ρ : Representation (ZMod l) H V)
    (m : ℕ) (hm : m ≤ finrank (ZMod l) V) :
    ∃ v : Fin m → V, LinearIndependent (ZMod l) v ∧
      ∀ h j, ρ h (v j) - v j ∈ Submodule.span (ZMod l) (v '' {i | i < j}) := by
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  induction m with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun _ j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hs⟩ := ih (Nat.le_of_succ_le hm)
    set U := Submodule.span (ZMod l) (Set.range v) with hU
    have hmono : ∀ j, Submodule.span (ZMod l) (v '' {i | i < j}) ≤ U := fun j =>
      Submodule.span_mono (Set.image_subset_range _ _)
    have hvU : ∀ j, v j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
    have hst : ∀ h, ∀ u ∈ U, ρ h u ∈ U := by
      intro h u hu
      have hle : U ≤ U.comap (ρ h) := by
        rw [hU, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have h1 := hmono j (hs h j)
        have h2 := U.add_mem h1 (hvU j)
        simpa using h2
      exact hle hu
    have hne : U ≠ ⊤ := by
      intro htop
      have h1 : finrank (ZMod l) U = m := by
        rw [hU, finrank_span_eq_card hv]; simp
      rw [htop, finrank_top] at h1
      omega
    obtain ⟨x, hx, hxs⟩ := hF l H hH V ρ U hst hne
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · exact (linearIndependent_finSnoc).2 ⟨hv, hx⟩
    · intro h j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · have himg : (Fin.snoc v x : Fin (m+1) → V) '' {i | i < Fin.last m} = Set.range v := by
          ext y
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hi' : i ≠ Fin.last m := ne_of_lt hi
            obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi'
            exact ⟨i', by simp⟩
          · rintro ⟨i, rfl⟩
            exact ⟨i.castSucc, Fin.castSucc_lt_last i, by simp⟩
        simp only [Fin.snoc_last]
        rw [himg]
        exact hxs h
      · have himg : v '' {i | i < j} ⊆ (Fin.snoc v x : Fin (m+1) → V) '' {i | i < j.castSucc} := by
          rintro _ ⟨i, hi, rfl⟩
          exact ⟨i.castSucc, by simpa using hi, by simp⟩
        simp only [Fin.snoc_castSucc]
        exact Submodule.span_mono himg (hs h j)

theorem flag_pf : FixVec → Flag := by
  intro hF l _ H _ hH V _ _ _ ρ
  classical
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite
  obtain ⟨v, hv, hs⟩ := exists_invariant_flag_mod_l hF l H hH V ρ _ le_rfl
  have hsp : ⊤ ≤ Submodule.span (ZMod l) (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (by simp)).ge
  let b : Basis (Fin (finrank (ZMod l) V)) (ZMod l) V := Basis.mk hv hsp
  refine ⟨b, ?_⟩
  intro h i j hji
  have hb : ∀ j, b j = v j := fun j => Basis.mk_apply hv hsp j
  have hmem : ρ h (b j) - b j ∈ Submodule.span (ZMod l) (b '' {i | i < j}) := by
    have : (b : _ → V) '' {i | i < j} = v '' {i | i < j} := by
      ext y; simp [hb]
    rw [this, hb]
    exact hs h j
  have hsupp := (Basis.mem_span_image b).1 hmem
  by_contra hne
  have hi : i ∈ ((b.repr (ρ h (b j) - b j)).support : Set _) := by
    simpa using hne
  have := hsupp hi
  exact absurd this (not_lt.2 hji)

end UpperTheory.Gal.Gen
