module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TotDisjUnlinked

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_val_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [val_absPow, LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq _).ne'),
    Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    ← Complex.exp_int_mul, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem absPow_eq_unrChar (s : ℂ) :
    absPow k s = unrChar k (Units.mk0 ((resCard k : ℂ) ^ (-s))
      (by
        have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
        exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq.ne')))) := by
  ext x
  rw [absPow_val_eq_zpow, unrChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end GlobalTheory.TotDisjUnlinked

theorem GlobalTheory.TotDisjUnlinked.main :
    GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.UnlinkedProductIrreducible := by
  intro H k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hu
  refine H k r t s s' π₁ π₂ d d' σ σ' h₁ h₂ fun a b h j _ => ?_
  rw [GlobalTheory.TotDisjUnlinked.absPow_eq_unrChar]
  exact hu a b h _
