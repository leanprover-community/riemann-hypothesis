module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPi
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

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi : ∀ {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (d : ℕ) (M : Set (Fin d → F)), (0 : Fin d → F) ∈ M → (∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) → (∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M) → (∀ i, Pi.single i 1 ∈ M) → (∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) → ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧ (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧ LinearIndependent F b := by
  first | exact @GlobalTheory.locBasis_of_bounded | exact GlobalTheory.locBasis_of_bounded | (intros; apply GlobalTheory.locBasis_of_bounded <;> assumption)
