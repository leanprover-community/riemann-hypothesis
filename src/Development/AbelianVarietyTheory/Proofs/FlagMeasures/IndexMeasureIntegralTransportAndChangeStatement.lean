module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChange
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

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_transport_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (Nice (A.map e.toAddMonoidHom) φ ↔ Nice A (fun w => φ (e w))) ∧ cint (A.map e.toAddMonoidHom) φ = cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (Nice A φ ↔ Nice A' φ) ∧ cint A' φ * (A.relIndex A' : ℂ) = cint A φ * (A'.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.Transport.cint_map_and_change | exact GlobalTheory.IdxInt.Transport.cint_map_and_change | (intros; apply GlobalTheory.IdxInt.Transport.cint_map_and_change <;> assumption)
