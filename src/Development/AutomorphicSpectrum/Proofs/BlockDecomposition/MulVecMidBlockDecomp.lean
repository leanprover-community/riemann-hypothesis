module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem qp_mulVec_midV_exists_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k) :
    ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  refine ⟨fun r => ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec
    (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) (Fin.castAdd t r), ?_⟩
  rw [GlobalTheory.CompanionTheory.BZPsiPG.topV_add_midV]
  funext r
  refine Fin.addCases (fun a => ?_) (fun b => ?_) r
  · rw [Fin.append_left]
  · rw [Fin.append_right]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_left,
      Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    rfl

end GlobalTheory.CompanionTheory.BZPsiPG
