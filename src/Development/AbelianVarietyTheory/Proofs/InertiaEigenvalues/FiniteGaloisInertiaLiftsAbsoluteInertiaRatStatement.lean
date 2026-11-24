module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
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

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField

theorem _root_.GlobalTheory.T.finiteGaloisInertia_lifts_absoluteInertia_rat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  first | exact @GlobalTheory.InertiaLift.main | exact GlobalTheory.InertiaLift.main | (intros; apply GlobalTheory.InertiaLift.main <;> assumption)
