module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DutySevenLibrary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory.BigTop

theorem famHyp_of_working_duty : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps),
    GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  intro 𝒜 eps Fm hW hD
  obtain ⟨⟨⟨⟨_, hDvd, _, hBox, hQD, hCYL⟩, hSm⟩, hTw⟩, hCE, hTu, hDG⟩ := hW
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm hD
  exact ⟨h1, h2, h3, h4, h5, hDvd, hBox, hQD, hCYL, hSm, hTw, hCE, hTu, hDG⟩

end GlobalTheory.BigTop
