module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_herbrandPhi_natCast_of_totallyRamified (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] :
    lowerRamificationGroup F L 0 = ⊤ → ∀ a : ℕ, (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L a =
      ((∑ t ∈ Finset.range a, Nat.card ↥(wild F L t) : ℕ) : ℝ) := by
  intro h0 a
  induction a with
  | zero => simp
  | succ n ih =>
    have hstep := herbrandPhi_of_mem_Icc (K := F) (L := L) n (u := ((n : ℝ) + 1))
      ⟨by linarith, le_refl _⟩
    have hidx : (lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex (lowerRamificationGroup F L 0) *
        Nat.card ↥(wild F L n) = Nat.card (L ≃ₐ[F] L) := by
      rw [h0, Subgroup.relIndex_top_right, wild, Subgroup.index_mul_card]
    have hpos : (0 : ℝ) < ((lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup F L 0) : ℝ) := relIndex_pos_of_finite _ _
    have hidxR : (((lowerRamificationGroup F L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup F L 0) : ℕ) : ℝ) * (Nat.card ↥(wild F L n) : ℝ) =
        (Nat.card (L ≃ₐ[F] L) : ℝ) := by exact_mod_cast hidx
    push_cast [Finset.sum_range_succ] at ih ⊢
    rw [hstep, ← ih, ← hidxR]
    field_simp
    ring

end GlobalTheory.PMon.Ram
