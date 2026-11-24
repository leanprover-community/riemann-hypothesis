module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramDifferenceEntryMemUniformizerPowIntegers
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

open Matrix

theorem _root_.GlobalTheory.T.gramDifference_entry_mem_uniformizerPow_integers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L)
  (x y : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  ϖ ∈ Formalism.UG.intL L → (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
  ∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweG.gramDiff_entry_int | exact GlobalTheory.Hk3.HoweG.gramDiff_entry_int | (intros; apply GlobalTheory.Hk3.HoweG.gramDiff_entry_int <;> assumption)
