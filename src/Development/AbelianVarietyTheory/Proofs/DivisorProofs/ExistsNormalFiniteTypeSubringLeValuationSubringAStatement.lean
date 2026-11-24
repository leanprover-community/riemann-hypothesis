module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringLeValuationSubringA
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

open Polynomial

theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_le_valuationSubring' : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ), (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) → (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) → ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R), ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring <;> assumption)
