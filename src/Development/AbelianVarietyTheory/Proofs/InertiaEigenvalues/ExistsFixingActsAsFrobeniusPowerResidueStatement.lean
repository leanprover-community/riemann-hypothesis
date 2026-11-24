module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixingActsAsFrobeniusPowerResidue
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

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_fixing_actsAsFrobeniusPowerResidue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  first | exact @GlobalTheory.GaloisLift.exists_fixing_actsAs | exact GlobalTheory.GaloisLift.exists_fixing_actsAs | (intros; apply GlobalTheory.GaloisLift.exists_fixing_actsAs <;> assumption)
