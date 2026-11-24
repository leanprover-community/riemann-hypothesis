module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed

@[expose] public section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.theta_basis_linear_combination : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (b b' : X.Fn l), b ∈ X.B N l w → b' ∈ X.B N l w → ∀ (c c' : ℤ_[l]) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l n b φ → IsThB X A N l n b' φ' →
    IsThB X A N l n (c • b + c' • b') (((c.appr n : ℕ) : Ω) • φ + ((c'.appr n : ℕ) : Ω) • φ') := by
  intro Ω _ _ _ ε X A N l _ n w b b' _ _ c c' φ φ' h h'
  obtain ⟨f, hfi, hfc, hfd, hfl⟩ := h
  obtain ⟨f', hfi', hfc', hfd', hfl'⟩ := h'
  refine ⟨f ^ (c.appr n) * f' ^ (c'.appr n), ?_, ?_, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact GlobalTheory.ThAdd.inv_mul (GlobalTheory.ThAdd.inv_pow hfi _) (GlobalTheory.ThAdd.inv_pow hfi' _)
  · rw [← GlobalTheory.ThAdd.cls_comb, ← hfc, ← hfc', ← map_smul, ← map_smul, ← map_add (f := _)]
    rfl
  · intro δ hδ hδ'
    obtain ⟨g, hgi, hg⟩ := hfd δ hδ hδ'
    obtain ⟨g', hgi', hg'⟩ := hfd' δ hδ hδ'
    refine ⟨g ^ (c.appr n) * g' ^ (c'.appr n), GlobalTheory.ThAdd.inv_mul (GlobalTheory.ThAdd.inv_pow hgi _) (GlobalTheory.ThAdd.inv_pow hgi' _), ?_⟩
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    calc (f : X.K) ^ (c.appr n) * (f' : X.K) ^ (c'.appr n) *
          (X.sl (ofSL δ) f ^ (c.appr n) * X.sl (ofSL δ) f' ^ (c'.appr n))
        = ((f : X.K) * X.sl (ofSL δ) f) ^ (c.appr n) * ((f' : X.K) * X.sl (ofSL δ) f') ^ (c'.appr n) := by ring
      _ = _ := by rw [hg, hg']; ring
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact GlobalTheory.ThAdd.isDl_mul (GlobalTheory.ThAdd.isDl_pow hfl _) (GlobalTheory.ThAdd.isDl_pow hfl' _)
