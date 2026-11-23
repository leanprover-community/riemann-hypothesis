module

import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingBump
public import Formalism.PeriodIntegrals.PhMeasCore
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

theorem mul_mem_UH {n : ℕ} {Hm a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH Hm) (hb : b ∈ UH Hm) :
    a * b ∈ UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_matMul {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) := by
  apply CompanionTheory.D.gk.admitted.Gard.contDiff_mul <;> assumption

theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * g) :=
  (@contDiff_matMul n).comp (contDiff_id.prodMk contDiff_const)

end Smooth

end PI.PhMeasCore.UnitaryGroupMassFormula

end
