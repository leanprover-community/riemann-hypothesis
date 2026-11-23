module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
import Formalism.LocalToGlobal.Columns.HeckeSpCount
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField Formalism.BasicNotions Formalism.L2.Col

theorem le_N_of_mem_gamRanks (R : Ranks) {n : ℕ} (hn : n ∈ gamRanks R) : n ≤ R.N R.m := by
  have hY : ∀ j, j ≤ R.m → R.rankY j ≤ R.N R.m := by
    intro j hj
    have : j * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ hj
    unfold Ranks.rankY Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have hm := R.two_le_m
  simp only [gamRanks, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, hj, rfl⟩ | rfl | rfl | rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj.2) _
  · exact hY _ le_rfl
  · exact hY _ (Nat.sub_le _ _)
  · simpa [Ranks.rankY, Ranks.nV] using hY 1 (by omega)

theorem DGam_dvd_of_minkMult : ∀ {X : Fields} (R : Ranks), X.Ok →
    ∀ M, Formalism.MainNotions.MinkMult (2 * X.f * R.N R.m) M → DGam X.E R ∣ M := by
  intro X R hX M hM
  have hE : Module.finrank ℚ X.E = 2 * X.f := by
    rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]
  refine DGam_dvd (posStar_of_ok hX) R fun a ha => ?_
  obtain ⟨n, hn, N, hN, hUni, rfl⟩ := Set.mem_iUnion₂.1 ha
  haveI := autO_finite (posStar_of_ok hX) (hcnt_isFullLattice_of_unimodular hN hUni)
  refine GlobalTheory.DGamOnRecord.card_dvd_of_minkMult hM ?_ _
  rw [hE]
  exact Nat.mul_le_mul_left _ (le_N_of_mem_gamRanks R hn)

end GlobalTheory.Mem.Col2
