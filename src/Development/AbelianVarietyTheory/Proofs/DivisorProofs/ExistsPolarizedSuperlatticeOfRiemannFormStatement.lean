module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.exists_polarized_superlattice_of_riemann_form : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  first | exact @GlobalTheory.UnimodOver.exists_unimodular_overlattice | exact GlobalTheory.UnimodOver.exists_unimodular_overlattice | (intros; apply GlobalTheory.UnimodOver.exists_unimodular_overlattice <;> assumption)
