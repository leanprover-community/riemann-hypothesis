module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU

theorem _root_.GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  first | exact @GlobalTheory.exists_holUnif_of_isExp | exact GlobalTheory.exists_holUnif_of_isExp | (intros; apply GlobalTheory.exists_holUnif_of_isExp <;> assumption)
