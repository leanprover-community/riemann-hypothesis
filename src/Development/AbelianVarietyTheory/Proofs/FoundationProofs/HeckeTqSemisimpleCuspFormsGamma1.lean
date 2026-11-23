module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspFormsStatement
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
import Mathlib.Tactic.Lemma
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

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne

lemma lev_one (N : ℕ) : GlobalTheory.Hk.lev N 1 = CongruenceSubgroup.Gamma1 N := by
  ext γ
  simp only [GlobalTheory.Hk.lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma0_mem, and_iff_left_iff_imp]
  intro _
  exact Subsingleton.elim _ _

theorem tq_semisimple : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N →
    IsDiam N 1 (q : ZMod N) σ →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ),
      (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N k q σ hN _ hq hqN hσ f c n h
  obtain ⟨-, -, hT, hD, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hT' : TqF (k : ℤ) q σ = GlobalTheory.Hk.heckeT (k : ℤ) q σ := funext fun F => hT _ _ _ F hq.pos
  have hσ' : GlobalTheory.Hk.IsDia N 1 (q : ℤ) σ := (hD N 1 (q : ℤ) σ).1 (by simpa using hσ)
  rw [hT'] at h ⊢
  let g : CuspForm (GlobalTheory.Hk.lev N 1) (k : ℤ) := f.copy ⇑f rfl (by rw [lev_one])
  exact GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms N 1 q (k : ℤ) σ c n (by omega) one_pos hq (by simpa using hqN) hσ' g h

end GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne
