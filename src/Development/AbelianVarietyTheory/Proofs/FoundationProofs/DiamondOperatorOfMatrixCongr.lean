module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMulInvMemGamma1InterGamma0LevelStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem dia_congr : ∀ (N l : ℕ) (k d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l d τ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k σ ⇑f = GlobalTheory.Hk.dia k τ ⇑f := by
  intro N l k d σ τ hN hσ hτ f
  have h := GlobalTheory.T.diamond_mul_inv_mem_gamma1InterGamma0Level N l d σ τ hN hσ hτ
  have hτ' : τ = (τ * σ⁻¹) * σ := by group
  have hinv : ⇑f ∣[k] (τ * σ⁻¹) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ h)
  unfold GlobalTheory.Hk.dia
  rw [hτ', SlashAction.slash_mul, hinv]

end GlobalTheory.Hk
