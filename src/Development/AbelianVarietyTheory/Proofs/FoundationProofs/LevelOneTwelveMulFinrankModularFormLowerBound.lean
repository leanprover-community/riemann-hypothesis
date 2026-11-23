module

public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem levelOne_twelve_mul_finrank_lower_bound :
    ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) +
      4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤
        12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  intro n hn
  rcases lt_or_ge n 0 with hneg | hpos
  · have h0 : (0 : ℤ) ≤ (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := Int.natCast_nonneg _
    obtain ⟨m, hm⟩ := hn
    generalize (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) = d at h0 ⊢
    split_ifs <;> omega
  · lift n to ℕ using hpos
    have hke : Even n := by exact_mod_cast hn
    have hrank := ModularForm.dimension_level_one n hke
    have hfin : Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) =
        if n % 12 = 2 then n / 12 else n / 12 + 1 := by
      exact Module.finrank_eq_of_rank_eq hrank
    obtain ⟨m, hm⟩ := hke
    generalize Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) = d at hfin ⊢
    split_ifs at hfin ⊢ <;> omega

end GlobalTheory.OddFrame
