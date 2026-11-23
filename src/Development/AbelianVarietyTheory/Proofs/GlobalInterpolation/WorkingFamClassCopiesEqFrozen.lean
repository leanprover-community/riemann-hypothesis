module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DutySevenLibrary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen
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
import Mathlib.Tactic.NormNum.Prime
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem copies_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (GlobalTheory.Cp.D3 3 𝒜 Fm ↔ W3 𝒜 Fm) ∧
    (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm ↔ W1 𝒜 Fm)) ∧
    ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → GlobalTheory.Cp.Duty Fm := by
  refine ⟨fun 𝒜 eps Fm => ⟨(working_classes_frozen.1 𝒜 eps Fm).2, (working_classes_frozen.1 𝒜 eps Fm).1⟩, fun eps Fm h => ?_⟩
  obtain ⟨a, b, c, d, e, f, g⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm h
  refine ⟨a, b, c, d, e, f, ?_⟩
  obtain ⟨x0, hx0⟩ := g
  exact ⟨x0, fun x hx hx1 i => hx0 x hx hx1 i⟩

end GlobalTheory.Fc
