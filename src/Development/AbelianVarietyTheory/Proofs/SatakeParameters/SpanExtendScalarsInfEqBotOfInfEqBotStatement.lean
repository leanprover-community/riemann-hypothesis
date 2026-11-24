module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Continuity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBot
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

@[expose] public section


theorem _root_.GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ → Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  first | exact @GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | exact GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | (intros; apply GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot <;> assumption)
