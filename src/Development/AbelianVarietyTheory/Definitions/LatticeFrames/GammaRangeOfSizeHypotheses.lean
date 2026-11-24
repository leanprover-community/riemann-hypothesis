module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
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
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def OneOn (S : Set ℝ) (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u

def SDiagOn (S : Set ℝ) (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), 1 ≤ large₂.CGam → TrueS D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def GamRange (D : D7) (L : ℝ) : Prop :=
  (D.R.m : ℝ) ^ 5 * D.R.f * L ≤ Real.log (AdmissibleBoundsFromSource.Gam D) ∧ 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k

theorem pow_five_mul_f_pos (D : D7) : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f := by
  have hf : 0 < D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  positivity

end GlobalTheory.Core.Diag
