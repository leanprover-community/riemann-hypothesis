module

public import Formalism.PeriodIntegrals.WeylForK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix

variable {N : ℕ}

def sPlus (ε : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun a => ε a = true)

def sMinus (ε : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun a => ε a = false)

def blk (ε : Fin N → Bool) : Fin (nPl ε) ⊕ Fin (nMi ε) ≃ Fin N :=
  (Equiv.sumCongr
    (((sPlus ε).orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight (fun a => by simp [sPlus])))
    (((sMinus ε).orderIsoOfFin rfl).toEquiv.trans
      (Equiv.subtypeEquivRight (p := fun a => a ∈ sMinus ε) (q := fun a => ¬ (ε a = true))
        (fun a => by simp [sMinus])))).trans
  (Equiv.sumCompl (fun a => ε a = true))

def ePl (ε : Fin N → Bool) (i : Fin (nPl ε)) : Fin N := blk ε (Sum.inl i)

def eMi (ε : Fin N → Bool) (j : Fin (nMi ε)) : Fin N := blk ε (Sum.inr j)

def iPl (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks h 0 0 1).submatrix (blk ε).symm (blk ε).symm

def iMi (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.fromBlocks 1 0 0 h).submatrix (blk ε).symm (blk ε).symm

def sPl {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin N → Bool)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ → (H →L[ℂ] H) :=
  fun h => σ (iPl ε h)

def sMi {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin N → Bool)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ → (H →L[ℂ] H) :=
  fun h => σ (iMi ε h)

def wu (n : ℕ) (μ : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b), (μ a - μ b + ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) /
    ∏ i ∈ Finset.range n, (i.factorial : ℝ)

end PI.WeylForKWork
