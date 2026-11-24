module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.NegSpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def neg (W : HSpace E) : HSpace E :=
  { W with
    hT := -W.hT
    herm := ⟨fun x y => by simpa using W.herm.eq x y⟩
    nondeg := ⟨fun x h => W.nondeg.1 x fun y => by simpa using h y,
      fun x h => W.nondeg.2 x fun y => by simpa using h y⟩
    sig := fun τ => ((W.sig τ).2, (W.sig τ).1)
    baseLattice_isUnimodular := by
      have h := W.baseLattice_isUnimodular
      have e : Formalism.HermitianLatticesTheory.dual (-W.hT) W.L0 = Formalism.HermitianLatticesTheory.dual W.hT W.L0 := by
        ext y
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
      unfold Formalism.HermitianLatticesTheory.IsUnimodular at h ⊢
      rw [e]; exact h }

theorem neg_rank (W : HSpace E) : (neg W).rank = W.rank := rfl

theorem neg_sig (W : HSpace E) (τ : E →+* ℂ) : (neg W).sig τ = ((W.sig τ).2, (W.sig τ).1) := rfl

end GlobalTheory.NegSpace
