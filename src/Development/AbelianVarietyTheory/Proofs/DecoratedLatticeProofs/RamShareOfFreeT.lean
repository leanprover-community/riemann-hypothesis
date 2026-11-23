module

public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeLineRamifiedFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem ramShare_of_freeT {D : D7} {u : D.what₂.Word} (W : Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) : RamShare D u := by
  have h := Formalism.MainNotions.product_first_zeroth_parts.rank_nat W
  have hT2 : 2 ≤ (D.mem u).A.T := ((D.mem u).A.T_prime).two_le
  unfold RamShare dU
  rw [d0_eq]
  have h' : ((D.mem u).A.du : ℝ) * (((D.mem u).A.T : ℝ) - 1) ^ D.R.f =
      (D.duS u : ℝ) * (((D.mem u).A.T : ℝ) - 2) ^ D.R.f := by
    have e2 : (D.mem u).A.T - 1 - 1 = (D.mem u).A.T - 2 := by omega
    rw [e2] at h
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_pow] at this
    rw [Nat.cast_sub (by omega : 1 ≤ (D.mem u).A.T), Nat.cast_sub hT2] at this
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
    linarith
  have e : (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) = (((D.mem u).A.T : ℝ) - 2) / (((D.mem u).A.T : ℝ) - 1) := by
    field_simp; ring
  rw [e, div_pow]
  have hne : (((D.mem u).A.T : ℝ) - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ hpos.ne'
  field_simp
  linarith [h']

theorem ramShare_of_trueD (D : D7) (u : D.what₂.Word) (hD : TrueD D) : RamShare D u :=
  TrueD.elim (Q := fun D => ∀ u : D.what₂.Word, RamShare D u)
    (fun _ _ _ _ _ w u => ramShare_of_freeT (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.freeT_0 (w.C.forms u).to0).some) hD u

end GlobalTheory.Core.Rk
