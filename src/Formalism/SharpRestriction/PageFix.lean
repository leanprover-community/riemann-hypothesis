module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
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

namespace Formalism.MainNotions

open Formalism.BasicNotions

def PageFix {eps : ℝ} (Fm : FamP eps) : Prop :=
  Fm.Cp = 1 ∧ Fm.eP = 12 ∧ Fm.cTO = 28 * Fm.eP + 41 ∧ Fm.Ct = Fm.cTO + 24 ∧ Fm.CetaF = 6 ∧ Fm.Cc = 2 ∧ Fm.cw = 9 / 10 ∧ Fm.CYL = 9 ∧
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    (Fm.D x i).host.ccK = ⊤ ∧
    (∀ τ τ', ((Fm.D x i).hc τ).v = ((Fm.D x i).hc τ').v) ∧
    (∀ j : Fin 2, (((Fm.D x i).host.g j : ℕ) : ℝ) ≤ Real.exp (9 * (Fm.L x i).sc.L)) ∧
    ((Fm.D x i).host.pde : ℝ) < (Fm.L x i).sc.X' ∧ ((Fm.D x i).host.pde' : ℝ) < (Fm.L x i).sc.X' ∧
    (Fm.L x i).j0 = ⌈Real.logb 5 (((Fm.D x i).R.n : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m / (Fm.D x i).R.m)⌉₊ ∧
    (Fm.D x i).host.Lw = 10 * ⌈(Fm.Ct + 4) * Real.log x⌉₊ + 2 * ⌈30 / eps⌉₊ + 22 ∧
    (Fm.parT x hx i).TO = ⌈x ^ Fm.cTO⌉₊

def PageWin {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (x ^ (2 + 8 * eps) ≤ ((Fm.D x i).R.n : ℝ) ∧ ((Fm.D x i).R.n : ℝ) ≤ 2 * x ^ (2 + 8 * eps)) ∧
    (Real.sqrt (x * (Fm.L x i).sc.delta1) ≤ ((Fm.D x i).R.m : ℝ) ∧
      ((Fm.D x i).R.m : ℝ) ≤ 2 * Real.sqrt (x * (Fm.L x i).sc.delta1)) ∧
    (x ^ (9 / 2 + 10 * eps) ≤ ((Fm.D x i).R.k : ℝ) ∧ ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * eps))

def WithPage (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ PageFix Fm

end Formalism.MainNotions

end
