module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
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
import Mathlib.RingTheory.Henselian
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

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory

theorem unitMinorSet_rank_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  intro k _ _ _ _ n d Y hY
  obtain ⟨-, f, hf⟩ := hY
  have hdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  have hunit : IsUnit (Y.submatrix id f) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsub : (Y.submatrix id f).rank = n := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  have hmul : Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f = Y.submatrix id f := by
    rw [Matrix.mul_submatrix_one]; rfl
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (Y.submatrix id f).rank := hsub.symm
    _ = (Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f).rank := by rw [hmul]
    _ ≤ Y.rank := Matrix.rank_mul_le_left _ _

end GlobalTheory
