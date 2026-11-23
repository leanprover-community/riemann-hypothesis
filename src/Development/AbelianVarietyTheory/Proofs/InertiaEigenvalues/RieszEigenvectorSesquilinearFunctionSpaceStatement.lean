module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RieszEigenvectorSesquilinearFunctionSpace
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


theorem _root_.GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  first | exact @GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | exact GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | (intros; apply GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space <;> assumption)
