module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
