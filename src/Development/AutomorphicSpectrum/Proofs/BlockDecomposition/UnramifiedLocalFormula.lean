module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianMatricesModPowStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSuccStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens Filter Topology

namespace GlobalTheory.CompanionTheory.UnrDens

theorem unrFormula : PositivityTheory.PfSWUS.Loc.UnrFormula := by
  intro R _ σ ϖ q ε hR m n hnm S T hS hT
  have hq : (0 : ℝ) < q := by exact_mod_cast lt_trans zero_lt_one hR.one_lt
  have hsq : n ^ 2 ≤ 2 * m * n := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a, 2 * m * n - n ^ 2 = a := ⟨_, rfl⟩
  have ha' : a + n ^ 2 = 2 * m * n := by omega
  have hsol : ∀ j : ℕ, (solCount σ ϖ S T (j + 1) : ℝ) =
      (q : ℝ) ^ a * (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) * (q : ℝ) ^ (j * a) := by
    intro j
    induction j with
    | zero =>
      rw [GlobalTheory.T.card_unimodular_hermitian_reps_level_one R σ ϖ q ε hR m n hnm S T hS hT, ha]
      simp
    | succ j ih =>
      rw [GlobalTheory.T.unimodular_hermitian_reps_count_succ R σ ϖ q ε hR m n hnm S T hS hT (j + 1) (by omega), ha]
      push_cast
      rw [ih, add_mul, one_mul, pow_add]
      ring
  have hdens : ∀ j : ℕ, densAt σ ϖ S T (j + 1) = ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
    intro j
    unfold densAt
    have hM : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (j + 1))) = q ^ (2 * (j + 1) * (m * n)) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ (j + 1)) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1), ← pow_mul,
        ← pow_mul]
      ring_nf
    rw [hsol j, GlobalTheory.T.card_hermitian_matrices_mod_pow R σ ϖ q ε hR n (j + 1), hM]
    have he : a + j * a + (j + 1) * n ^ 2 = 2 * (j + 1) * (m * n) := by
      calc a + j * a + (j + 1) * n ^ 2 = (j + 1) * (a + n ^ 2) := by ring
        _ = (j + 1) * (2 * m * n) := by rw [ha']
        _ = 2 * (j + 1) * (m * n) := by ring
    have hpos : (0 : ℝ) < (q : ℝ) ^ (2 * (j + 1) * (m * n)) := pow_pos hq _
    push_cast
    rw [div_eq_iff hpos.ne', ← he, pow_add, pow_add]
    ring
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hdens j).symm

end GlobalTheory.CompanionTheory.UnrDens
