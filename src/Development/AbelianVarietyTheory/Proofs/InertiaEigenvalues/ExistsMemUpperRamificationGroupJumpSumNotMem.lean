module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_upperRamificationGroup_jumpSum_not_mem :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)),
      lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ →
        ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B h0 hB
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 n
  simp only [top_inf_eq] at hjs hn
  have hcard : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hidx : (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) = herbrandPhi F L n := by
    rw [hjs, ← hphi]
    field_simp
  rw [hidx, upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]
  cases n with
  | zero =>
    obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ B := by
      by_contra h
      push_neg at h
      exact hB (eq_top_iff.mpr fun σ _ => h σ)
    refine ⟨σ, ?_, hσ⟩
    rw [Nat.cast_zero, h0]
    exact Subgroup.mem_top σ
  | succ k =>
    have hk : ¬ wild F L k ≤ B := (hn k).mp (Nat.lt_succ_self k)
    obtain ⟨σ, hσ, hσB⟩ := SetLike.not_le_iff_exists.mp hk
    refine ⟨σ, ?_, hσB⟩
    have : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [this]
    exact hσ

end GlobalTheory.PMon.Ram
