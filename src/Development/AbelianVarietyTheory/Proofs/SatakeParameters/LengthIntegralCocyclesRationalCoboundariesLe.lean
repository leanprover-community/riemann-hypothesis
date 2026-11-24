module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RepresentationTheory.Invariants
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

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

namespace GlobalTheory

theorem cocycle_bound_length_le : ∀ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (Z : Submodule O (G → V)), (∀ c ∈ Z, ∀ g, c g ∈ L.T) → Module.length O (↥(Z ⊓ (B1 ρ).restrictScalars O) ⧸ (latticeCoboundaries L).comap (Z ⊓ (B1 ρ).restrictScalars O).subtype) ≤ Module.length O ↥(Representation.invariants (repD L)) := by
  intro G _ LL _ O _ _ V _ _ _ _ ρ L Z hZ
  set M := Z ⊓ (B1 ρ).restrictScalars O with hM
  set K := (latticeCoboundaries L).comap M.subtype with hK

  let χ : V →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ (cob ρ).restrictScalars O
  have hχ : L.T ≤ LinearMap.ker χ := by
    intro t ht
    simp only [LinearMap.mem_ker, χ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨t, ht, rfl⟩
  let ψ : ↥(Representation.invariants (repD L)) →ₗ[O] (G → V) ⧸ latticeCoboundaries L :=
    (L.T.liftQ χ hχ) ∘ₗ (Representation.invariants (repD L)).subtype
  let ι : M →ₗ[O] (G → V) ⧸ latticeCoboundaries L := (latticeCoboundaries L).mkQ ∘ₗ M.subtype
  have hKι : K ≤ LinearMap.ker ι := by
    intro x hx
    simpa [ι, K, Submodule.Quotient.mk_eq_zero] using hx
  let f : (M ⧸ K) →ₗ[O] (G → V) ⧸ latticeCoboundaries L := K.liftQ ι hKι
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K x
    simp only [LinearMap.mem_ker, f, Submodule.liftQ_apply, ι, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, K, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact hx
  have hrange : LinearMap.range f ≤ LinearMap.range ψ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨⟨c, hcM⟩, rfl⟩ := Submodule.Quotient.mk_surjective K x
    obtain ⟨hcZ, hcB⟩ := hcM
    obtain ⟨v, hv⟩ := hcB
    have hinv : L.T.mkQ v ∈ Representation.invariants (repD L) := by
      intro g
      change (Submodule.Quotient.mk ((ρ g) v) : V ⧸ L.T) = Submodule.Quotient.mk v
      rw [Submodule.Quotient.eq]
      have := hZ c hcZ g
      rw [← hv] at this
      simpa [cob] using this
    refine ⟨⟨_, hinv⟩, ?_⟩
    simp [ψ, f, ι, χ, hv]
  calc Module.length O (M ⧸ K) ≤ Module.length O (LinearMap.range ψ) :=
        Module.length_le_of_injective ((Submodule.inclusion hrange).comp f.rangeRestrict) (by
          intro a b hab
          apply hfinj
          have := congrArg Subtype.val hab
          simpa using this)
    _ ≤ _ := Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict

end GlobalTheory
