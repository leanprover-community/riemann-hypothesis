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

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.UnitMinorStable

theorem mul_mem_unitMinorSet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  intro k _ _ _ _ n d E Y hE hY
  obtain ⟨hYi, f, hf⟩ := hY
  have hEi := ((GlobalTheory.SplitFlip.mem_KO_iff E).1 hE).1
  refine ⟨fun i j => ?_, f, ?_⟩
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hEi i l) (hYi l j)
  · have hsub : (E.val * Y).submatrix id f = E.val * Y.submatrix id f := by
      ext i j; rfl
    have hdet := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hE
    have hg : ((GlobalTheory.SplitFlip.gdet E : kˣ) : k) = E.val.det := rfl
    rw [hsub, Matrix.det_mul, map_mul, hf, mul_one, ← hg, hdet]

end GlobalTheory.UnitMinorStable
