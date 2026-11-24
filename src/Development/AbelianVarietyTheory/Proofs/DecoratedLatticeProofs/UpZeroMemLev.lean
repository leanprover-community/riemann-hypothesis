module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

def xZero (κ t : Type) : κ ≃ XIx κ t 0 := (Equiv.sumEmpty κ (Fin 0)).symm.trans (Equiv.sumEmpty (κ ⊕ Fin 0) (Fin 0 × t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def upZero : GL (Fin κ ⊕ Fin (s + 1)) k ≃* GL (XIx (Fin κ) t 0 ⊕ Fin (s + 1)) k :=
  (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t)).trans (typeFrame S.ϖ (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _))).conj

theorem upZero_apply (x : GL (Fin κ ⊕ Fin (s + 1)) k) : upZero S t x =
    (S.T t).bas 0 (s + 1) (Nat.zero_add _) *
      reGL (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)) (reGL (ixZero (Fin κ ⊕ Fin (s + 1)) t) x) *
      ((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹ := rfl


open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {s κ : ℕ} (S : _root_.GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] in
theorem _root_.GlobalTheory.LevZeroGen.upZero_mem_lev (x : GL (Fin κ ⊕ Fin (s + 1)) k) :
    _root_.GlobalTheory.LevZeroGen.upZero S t x ∈
        ((S.T t).lev 0 (s + 1)
          (Nat.zero_add _)).J ↔
      x ∈ S.P.J := by
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, _root_.GlobalTheory.LevZeroGen.upZero,
    MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply]
  rw [_root_.GlobalTheory.StepData.TypeDatum.iter_zero]
  unfold _root_.GlobalTheory.StepData.TypeDatum.reindex
  show _ ∈ (_root_.GlobalTheory.StepData.Level.map _ _).J ↔ _
  rw [_root_.GlobalTheory.StepData.Level.mem_map, MulEquiv.symm_apply_apply]

end GlobalTheory.LevZeroGen
end
