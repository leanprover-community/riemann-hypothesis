module

import Formalism.MahlerMeasure.MahlerMeasureProofs.FockBlocks
public import Formalism.MahlerMeasure.LevelLattice
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section block
variable {N r : ℕ} (D : BlockData N)

def wv (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i), c)
def ev (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i + 1), c)
def zi (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalZ N r D.T.t (Fin.castSucc i)
def si (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalS N r D.T.t (Fin.castSucc i)
def wU (c : Fin r) : BVar N r D.T.t := Sum.inl (Fin.castSucc D.uPos, c)
def zP (r : ℕ) : BVar N r D.T.t := scalZ N r D.T.t (Fin.last D.T.t)
def sP (r : ℕ) : BVar N r D.T.t := scalS N r D.T.t (Fin.last D.T.t)

variable {D}

theorem pos_succ_lt (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 + 1 < N := by
  obtain ⟨_, h2, _, h4⟩ := hB
  have := h2 i
  omega

theorem finPos_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (finPos N (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) N = D.T.pos i
  omega

theorem finPos_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (finPos N (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) N = D.T.pos i + 1
  omega

theorem letterAt_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (D.letterAt (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) (N - 1) = D.T.pos i
  omega

theorem letterAt_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (D.letterAt (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) (N - 1) = D.T.pos i + 1
  omega

theorem pos_inj (hB : D.BlockOK) {i i' : Fin D.T.t} (h : D.T.pos i = D.T.pos i') : i = i' := hB.1.1.injective h

theorem pos_ne_succ (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨hi, hti, _⟩ := hB.1.2.1 i
  obtain ⟨hi', _, hfi'⟩ := hB.1.2.1 i'
  have e : D.LL.vec ⟨D.T.pos i, by omega⟩ = D.LL.vec ⟨D.T.pos i' + 1, hi'⟩ := congrArg D.LL.vec (Fin.ext h)
  rw [hti, hfi'] at e
  exact absurd e (by decide)

theorem pos_lt_u (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 < (D.uPos : ℕ) := hB.2.1 i

theorem deg_lettersAt_pos (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) = D.LL.deg (D.letterAt (D.T.pos i)) - j i := by
  apply Formalism.GM.FockB.deg_fst <;> assumption

theorem deg_lettersAt_pos_succ (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  apply Formalism.GM.FockB.deg_snd <;> assumption

theorem deg_U (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  simp only [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  rw [Finset.sum_eq_zero (fun b _ => by
      rw [if_neg]
      have := pos_lt_u hB b
      omega)]
  simp

end block

end Formalism.InvariantFactorPaths.KP.LL
