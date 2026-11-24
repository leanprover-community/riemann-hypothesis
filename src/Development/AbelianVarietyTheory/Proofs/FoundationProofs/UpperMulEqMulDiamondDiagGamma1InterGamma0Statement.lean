module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperMulEqMulDiamondDiagGamma1InterGamma0
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.upper_mul_eq_mul_diamond_diag_gamma1InterGamma0 : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  first | exact @GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | exact GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag | (intros; apply GlobalTheory.Hk.upper_mul_eq_mul_diamond_diag <;> assumption)
