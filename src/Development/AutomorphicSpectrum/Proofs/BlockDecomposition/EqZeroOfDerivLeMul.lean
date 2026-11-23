module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.GronwallZero

theorem eq_zero_of_deriv_le_mul :
    ∀ (e e' : ℝ → ℝ) (K t : ℝ), 0 ≤ t → (∀ s, HasDerivAt e (e' s) s) →
      (∀ s, e' s ≤ K * e s) → (∀ s, 0 ≤ e s) → e 0 = 0 → e t = 0 := by
  intro e e' K t ht hd hle hnn h0
  have hg : ∀ s, HasDerivAt (fun s => e s * Real.exp (-K * s))
      ((e' s - K * e s) * Real.exp (-K * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-K * s)) (Real.exp (-K * s) * (-K)) s := by
      have h2 : HasDerivAt (fun s : ℝ => -K * s) (-K) s := by
        simpa using (hasDerivAt_id s).const_mul (-K)
      exact h2.exp
    have h5 : HasDerivAt (fun s => e s * Real.exp (-K * s))
        (e' s * Real.exp (-K * s) + e s * (Real.exp (-K * s) * (-K))) s := (hd s).mul h1
    exact h5.congr_deriv (by ring)
  have hanti : Antitone (fun s => e s * Real.exp (-K * s)) := by
    apply antitone_of_deriv_nonpos
    · exact fun s => (hg s).differentiableAt
    · intro s
      rw [(hg s).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle s]) (Real.exp_pos _).le
  have h3 : e t * Real.exp (-K * t) ≤ e 0 * Real.exp (-K * 0) := hanti ht
  rw [h0, zero_mul] at h3
  have h4 : e t ≤ 0 := by
    by_contra hc
    exact absurd h3 (not_le.mpr (mul_pos (not_le.mp hc) (Real.exp_pos _)))
  exact le_antisymm h4 (hnn t)

end GlobalTheory.CompanionTheory.WaveSpd.GronwallZero
