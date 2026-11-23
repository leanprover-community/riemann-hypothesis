module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenLeOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTameStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfIsPullbackOfSurjectiveOfFlat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem exists_smooth_descent_of_tame_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X X' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) (s : X ⟶ Sp R) (τ : Γ →* Aut G.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsFinite π → IsQProjOver (G.hom ≫ s) → Smooth G.hom → (∀ g, (τ g).asIso.hom ≫ G.hom = G.hom ≫ (ρ g).asIso.hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst G.hom x ≫ (τ g).asIso.hom = pullback.fst G.hom x) → ∃ (G' : Over X') (φ : G.left ⟶ G'.left), IsPullback φ G.hom G'.hom π ∧ Smooth G'.hom ∧ ∀ g, (τ g).asIso.hom ≫ φ = φ := by
  intro Γ _ _ R _ X X' _ ρ π G s τ hπ hfin hqp hsm hτ hstab hfib
  have hsepG : G.left.IsSeparated := by
    obtain ⟨N, i, hi, -, hcomp⟩ := hqp
    haveI := isProper_str R N
    haveI : IsSeparated (G.hom ≫ s) := by rw [← hcomp]; infer_instance
    constructor
    rw [show terminal.from G.left = (G.hom ≫ s) ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨Y', φ, hφ⟩ := exists_quotient_of_finite_group Γ G.left τ (fun y => by
    obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver R G.left (G.hom ≫ s) hqp
      (Set.range fun g => (τ g).asIso.hom y) ⊤ (Set.finite_range _) (fun _ _ => trivial)
    exact ⟨V, hV, fun g => hF ⟨g, rfl⟩⟩)
  obtain ⟨p', hp', -⟩ := quotient_existsUnique_comp_eq Γ G.left Y' τ φ hφ X' (G.hom ≫ π)
    (fun g => by rw [← Category.assoc, hτ g, Category.assoc, hπ.2.1 g])
  obtain ⟨hpb, hflat, hlft⟩ := GlobalTheory.T.isPullback_flat_of_tame_alt Γ X X' G.left Y' ρ τ π φ G.hom p' hπ hφ hp' hτ hfin
    inferInstance inferInstance hstab hfib
  have hsurj : Surjective π := (quotient_isIntegral_surjective_orbits Γ X X' ρ π hπ).2.1
  haveI : LocallyOfFinitePresentation p' := inferInstance
  exact ⟨Over.mk p', φ, hpb,
    smooth_of_isPullback_of_surjective_of_flat X X' G.left Y' π φ G.hom p' hpb hsurj hflat
      inferInstance hsm, fun g => hφ.2.1 g⟩

end GlobalTheory
