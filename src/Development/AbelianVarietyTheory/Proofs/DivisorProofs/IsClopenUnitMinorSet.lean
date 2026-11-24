module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem isClopen_setOf_valuation_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsClopen {x : k | valuation k x = 1} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    rw [IsValuativeTopology.mem_nhds_iff']
    by_cases h0 : y = 0
    · subst h0
      refine ⟨1, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_one, sub_zero, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      exact hz.ne
    · have hv : valuation k y ≠ 0 := by simpa using h0
      refine ⟨Units.mk0 _ hv, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      have : z = y + (z - y) := by ring
      rw [this, (valuation k).map_add_eq_of_lt_left hz]
      exact hy
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [IsValuativeTopology.mem_nhds_iff']
    refine ⟨1, fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Set.mem_setOf_eq] at hz hy ⊢
    have : z = y + (z - y) := by ring
    rw [this, (valuation k).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem isClopen_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) : IsClopen (unitMinorSet k n d) := by
  have hI : IsClopen {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    exact ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hU : IsClopen (⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1}) := by
    refine isClopen_iUnion_of_finite fun f ↦ (isClopen_setOf_valuation_eq_one k).preimage ?_
    exact Continuous.matrix_det (Continuous.matrix_submatrix continuous_id _ _)
  have e : unitMinorSet k n d = {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} ∩ ⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1} := by
    ext Y; simp [unitMinorSet]
  rw [e]; exact hI.inter hU

end GlobalTheory.FullRankCoinv.UnitMinor
