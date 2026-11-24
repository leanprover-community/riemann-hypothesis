module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsToLatticeOfFiniteInvertibleStabilisers
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


theorem _root_.GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  first | exact @GlobalTheory.lift_forms_of_card_isUnit | exact GlobalTheory.lift_forms_of_card_isUnit | (intros; apply GlobalTheory.lift_forms_of_card_isUnit <;> assumption)
