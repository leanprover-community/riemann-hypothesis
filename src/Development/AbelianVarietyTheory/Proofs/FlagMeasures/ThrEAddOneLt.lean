module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
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

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.DsigSize

theorem thrE_add_one_lt {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) :
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
  have hn := Formalism.MainNotions.nS_cast D
  have h6 := Formalism.MainNotions.six_le_n D
  rw [← hn] at h6 ⊢
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ)
  have hthr : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3 :=
    Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith only [h6])
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ (by linarith only [h6])
  have hn16 : 6 ≤ n ^ 16 :=
    (show (6 : ℝ) ≤ 6 ^ 16 by norm_num).trans (pow_le_pow_left₀ (by norm_num) h6 16)
  calc
    _ < 4 * n ^ 3 + 2 := by linarith only [hthr]
    _ ≤ 6 * n ^ 3 := by linarith only [hn3]
    _ ≤ n ^ 16 * n ^ 3 := mul_le_mul_of_nonneg_right hn16 (by positivity)
    _ = n ^ 19 := (pow_add n 16 3).symm
    _ ≤ n ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
    _ ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) :=
      le_mul_of_one_le_left (by positivity) hCL
    _ = Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ac_rfl

theorem dsigHC : Formalism.L2.SG.Pf.SzHypFD.DsigHC := by
  intro D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ
  exact GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.MainNotions.BridgeLemma.szh_hc hH τ) (Formalism.MainNotions.BridgeLemma.szh_gap hH τ)
    (thrE_add_one_lt hH hCL)

end GlobalTheory.DsigSize
