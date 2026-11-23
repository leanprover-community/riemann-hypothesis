module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingFamClassCopiesEqFrozen
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
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

theorem _root_.GlobalTheory.T.workingFamClass_copies_eq_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (GlobalTheory.Cp.D3 3 𝒜 Fm ↔ W3 𝒜 Fm) ∧ (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm ↔ W1 𝒜 Fm)) ∧ ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → GlobalTheory.Cp.Duty Fm := by
  first | exact @GlobalTheory.Fc.copies_frozen | exact GlobalTheory.Fc.copies_frozen | (intros; apply GlobalTheory.Fc.copies_frozen <;> assumption)
