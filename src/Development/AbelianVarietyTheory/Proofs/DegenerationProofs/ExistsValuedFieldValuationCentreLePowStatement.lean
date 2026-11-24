module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePow
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


theorem _root_.GlobalTheory.T.exists_valuedField_valuationCentre_le_pow : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (u : R), u ∈ IsLocalRing.maximalIdeal R → u ≠ 0 → ∀ R₁ : Subalgebra R K, Module.Finite R R₁ → ∀ S : ValuationSubring K, (∀ r, algebraMap R K r ∈ S) → ∀ e : ℕ, ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ‖gam (algebraMap R K u)‖ < 1 ∧ ∀ f ∈ R₁, S.valuation f < 1 → ‖gam f‖ < 1 ∧ (S.valuation (algebraMap R K u) = 1 → ‖gam f‖ ≤ ‖gam (algebraMap R K u)‖ ^ e) := by
  first | exact @GlobalTheory.exists_valuedField_centre_le_pow | exact GlobalTheory.exists_valuedField_centre_le_pow | (intros; apply GlobalTheory.exists_valuedField_centre_le_pow <;> assumption)
