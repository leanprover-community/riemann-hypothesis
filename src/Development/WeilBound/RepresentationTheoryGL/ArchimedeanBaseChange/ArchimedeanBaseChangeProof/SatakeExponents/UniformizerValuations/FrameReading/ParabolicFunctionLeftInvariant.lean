module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


namespace PositivityTheory.Rg.BcB.F.Tail.B

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_entries {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = m.1.val i j) ∧
      ∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = m.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] <;> rfl

theorem blocks_of_blk_mem {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (hk : blk h w m X ∈ GlobalTheory.LFun.KGL w (n := n)) :
    m.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ m.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [CtLevel.blk_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w m X).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w _ _).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w m X).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w _ _).2] at this

end PositivityTheory.Rg.BcB.F.Tail.B

end
