module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.flag_potential_levi_form_cell :
    ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ),
    let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j)
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧
      levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w =
        ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2)
          then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | exact GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell <;> assumption)
