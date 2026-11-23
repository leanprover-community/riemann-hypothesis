module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantTuplePrescribedMemberLinearForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_dominant_tuple_prescribed_member_linearForm : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a₀ : Fin m → X), IsCone bar φ γ → NoEquivRays O γ → (∀ x, x ≠ 0 → ∃ j, 0 < γ j x x) → Supports bar φ d γ a₀ → ∀ (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ), PosW W → ∀ N₁ : ℕ, 3 ≤ N₁ → ∀ lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ lam (γ j)) → ∀ μ : Fin (s + 1) → X, ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧ Dominant bar φ (D * d) N₁ W γ a ∧ ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  first | exact @GlobalTheory.Poinc.DomTuple.exists_dominant | exact GlobalTheory.Poinc.DomTuple.exists_dominant | (intros; apply GlobalTheory.Poinc.DomTuple.exists_dominant <;> assumption)
