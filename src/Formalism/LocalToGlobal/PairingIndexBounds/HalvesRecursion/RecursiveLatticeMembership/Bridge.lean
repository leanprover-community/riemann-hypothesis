module

public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem HfS_apply (D : D7) (T : Tor D) (N N' : ℕ) (z w : VC D N N') : HfS D T N N' z w = Hf D T z w := rfl

theorem al_pm (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : al D T x = 1 ∨ al D T x = -1 := by
  unfold al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re)) with h | h
  · left; exact h.neg_one_zpow
  · right; exact h.neg_one_zpow

theorem exp_int_sign (b : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (b : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

theorem local_global_comparison_holds : Bridge := by
  intro D T N N'
  refine ⟨fun x y => ?_, fun x G => rfl, fun La₁ La₂ G => ?_, fun La' G hG => ?_, fun La' hI => ?_⟩
  · show Hf D T y x = starRingEnd ℂ (Hf D T x y)
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T x y
  · funext z
    simp only [Iop, inter, relIdx, AddSubgroup.relIndex]
    rfl
  · intro x hx z
    exact hG.2 x hx z
  · refine ⟨fun x _ => al_pm D T x, fun x hx y hy => ?_⟩
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_HfInt T hI x hx y hy
    rw [h]
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (Hf D T x y).im = b := by rw [hab]; simp
    simp only [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf, altE, HfS_apply, him]
    have e := exp_int_sign b
    push_cast at e ⊢
    rw [e]

end Formalism.L2.PairingIndexBounds.Rec
