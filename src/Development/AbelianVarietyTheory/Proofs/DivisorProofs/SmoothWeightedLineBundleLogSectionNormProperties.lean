module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ContDiff

namespace GlobalTheory.Mix.SecNorm

theorem logSec_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  intro k _ X p σ M s
  have hpos : ∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s) := fun y => by
    rw [← secVal_ne_zero_iff s (mem_pick M.φ.isLB y), Weight.nsq, mul_pos_iff_of_pos_right (Real.exp_pos _),
      sq_pos_iff, norm_ne_zero_iff]
  refine ⟨?_, hpos, fun y => ?_, fun u hu y hy => ?_⟩
  · exact (Real.measurable_log.comp (M.cInf.continuous_nsq s).measurable).div_const 2
  · have hi := mem_pick M.φ.isLB y
    have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi
    have h1 : CInfAt (fun z => ‖ev p σ (M.B.U (pick M.φ.isLB y)) (s.f _) z‖ ^ 2) y :=
      ⟨_, Unit, inferInstance, fun _ => s.f _, fun v => ‖v ()‖ ^ 2, univ, hi, isOpen_univ, trivial,
        ((contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
    refine (h1.comp₂ (M.cInf _ y hi) (G := fun x => x.1 * Real.exp (-x.2))
      (contDiff_fst.mul contDiff_snd.neg.exp)).congr ?_
    exact eventually_of_mem ho fun z hz => M.φ.nsq_eq (secVal_mem s) hz
  · have h := (hpos y).2 hy
    change Real.log ((M.φ.addFn u).nsq (secVal p σ s) y) / 2 = Real.log (M.φ.nsq (secVal p σ s) y) / 2 - u y / 2
    rw [Weight.nsq_addFn, Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

end GlobalTheory.Mix.SecNorm
