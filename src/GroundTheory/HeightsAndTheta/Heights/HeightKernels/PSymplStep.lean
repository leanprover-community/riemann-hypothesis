module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplStep.proof (h1 : SymplFirstRow.Statement) (h2 : SymplGramMem.Statement)
    (h3 : SymplReduceMem.Statement) (h4 : SymplReducePosDef.Statement)
    (h5 : SymplReduceStep.Statement) : SymplStep.Statement := by
  intro n B G hG hGpd hind
  obtain ⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩ := h1 n G hG hGpd
  obtain ⟨hHmem, hHpd, hcomp, -⟩ := h2 (n + 1) P₁ G hP₁ hG hGpd
  have hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    rw [hP₁e]; exact hpos.ne'
  obtain ⟨Q, hQ, hQB⟩ :=
    hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)
  obtain ⟨Q', hQ', hQ'e, hQ'det⟩ := h5 n (symplGram P₁ G) Q hHe hQ
  refine ⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩
  · rw [hcomp Q', hQ'e, hP₁e]
  · rw [hcomp Q', hQ'det, hP₁e]
    exact mul_le_mul_of_nonneg_left hQB hpos.le

end GroundTheory.Heights₂.Heights
