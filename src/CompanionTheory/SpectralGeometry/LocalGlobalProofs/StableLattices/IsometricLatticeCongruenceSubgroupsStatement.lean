module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsometricLatticeCongruenceSubgroups
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.isometric_lattice_congruence_subgroups : StDelta → StExists → StFrame → StTor → StDecomp → StIwahori → (∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L), (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)), IsLat L Λ → (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J), (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧ (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧ IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧ ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧ ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U) → StCartanU := by
  first | exact @GlobalTheory.CompanionTheory.CartanU.final | exact GlobalTheory.CompanionTheory.CartanU.final | (intros; apply GlobalTheory.CompanionTheory.CartanU.final <;> assumption)
