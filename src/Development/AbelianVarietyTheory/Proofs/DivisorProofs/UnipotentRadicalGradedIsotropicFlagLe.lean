module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem unipFlag_castLE_le_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hs0 : s = 0 := by
      by_contra h0
      obtain ⟨k, hk, -⟩ := (hS ⟨0, by omega⟩).1 (by simp only; omega)
      simp at hk
    subst hs0
    rw [GlobalTheory.StdPar.unip_empty]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    obtain ⟨a, ha⟩ := hg.2 (Pi.single j 1) (Subsingleton.elim _ _)
    have h0 : adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = 0 := funext fun _ => by simp [Matrix.mulVec, dotProduct]
    have hv : (fun i => inclR (F := F) (AF F) ((Pi.single j (1 : E) : Fin n → E) i)) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    rw [h0, hv, sub_mulVec, one_mulVec, sub_eq_zero, mulVec_single_one] at ha
    exact (congrFun ha i).trans (Pi.single_apply _ _ _)
  · obtain ⟨m, hmS, hmax⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩
    have hsm : s = m.val + 1 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk, hle⟩ := (hS ⟨m.val + 1, by omega⟩).1 (by simp only; omega)
        have h2 := hmax k hk
        rw [Fin.le_def] at hle h2
        simp only at hle
        omega
      · have := (hS m).2 ⟨m, hmS, le_rfl⟩
        omega
    subst hsm
    have hd' : d = fun i => (S.filter fun k => k.val < i.val).card := by
      funext i
      rw [hd i]
      congr 1
    subst hd'
    exact GlobalTheory.FlagRad.unipFlag_le_unip F E σ h n J hJ r X Y hW S m hmS hmax

end GlobalTheory.TieStd
