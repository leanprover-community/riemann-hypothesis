module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.HerbrandB
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] {M : Type u} [AddCommGroup M] [Module k M]

theorem nonempty_of_surjective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (H : AddSubgroup X)
    (φ : X →+ Y) (hφ : Surjective φ) (hk : ∀ x, φ x = 0 ↔ x ∈ H) : Nonempty (Y ≃+ X ⧸ H) := by
  have : φ.ker = H := by ext x; rw [AddMonoidHom.mem_ker, hk]
  subst this
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm⟩

theorem nonempty_groupCohomology_even (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi0 : i ≠ 0) (hi : Even i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ TateZerothCohomology ρ g) := by
  have : NeZero i := ⟨hi0⟩
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπEven]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff (Rep.of ρ) g hg i hi x

theorem nonempty_groupCohomology_odd (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ H1 ρ g) := by
  let π := Rep.FiniteCyclicGroup.groupCohomologyπOdd (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπOdd]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (Rep.of ρ) g hg i hi x

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
