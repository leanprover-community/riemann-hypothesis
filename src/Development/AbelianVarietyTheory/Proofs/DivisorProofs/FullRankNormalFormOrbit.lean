module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Formalism.DoubleCosetMeasures.Statement
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

namespace GlobalTheory.FullRankCoinv

theorem exists_eq_normal_form_mul_of_rank_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (hnd : n ≤ d)
    (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  let σ : Fin n ⊕ Fin (d - n) ≃ Fin d :=
    (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσ : ∀ i : Fin n, ((σ (Sum.inl i) : Fin d) : ℕ) = d - n + i := fun i => by
    simp [σ]
  have hX : X0 k σ = GlobalTheory.FullRankCoinv.Y0 k n d := by
    ext i j
    simp only [X0, GlobalTheory.FullRankCoinv.Y0, Matrix.of_apply]
    congr 1
    apply propext
    rw [← hσ i, eq_comm]
    exact Fin.val_inj.symm
  have hc : Y.rank = Fintype.card (Fin n) := by simpa using hY
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ Y).1 hc
  exact ⟨invT h, by rw [hh, hX]⟩

end GlobalTheory.FullRankCoinv
