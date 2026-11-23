module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GraphIdeal
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

theorem smoothNear_comp_init {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {g : (Fin n → ℂ) → ℝ} (hg : SmoothNear (zeroSet J) g) :
    SmoothNear (zeroSet (graphIdeal J p)) (fun x => g (Fin.init x)) := by
  obtain ⟨U, hU, hJU, hgU⟩ := hg
  have hinit : ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℂ => Fin.init x) :=
    contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℂ) (Fin.castSucc i)
  exact ⟨(fun x => Fin.init x) ⁻¹' U, hU.preimage hinit.continuous,
    fun x hx => hJU (init_mem_zeroSet p hx), hgU.comp hinit.contDiffOn fun _ hx => hx⟩

theorem linEval_single_last {n : ℕ} (x : Fin (n + 1) → ℂ) :
    linEval (Pi.single (Fin.last n) 1) x = x (Fin.last n) := by
  simp [linEval, Pi.single_apply]

end GroundTheory.Heights₂.Heights.Targets
