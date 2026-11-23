module

public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CochainInjectiveExact
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicTrivialInductionRing
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomologyFiniteShortExact
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

private theorem isDiscreteRep_of_forall_eq {k G : Type} [CommRing k] [Group G]
    [TopologicalSpace G] (A : Rep.{0, 0, 0} k G) (h : ∀ (g : G) (a : A.V), A.ρ g a = a) :
    GroundTheory.ProfCoh.IsDiscreteRep A := by
  have : A.ρ.IsTrivial := ⟨fun g => LinearMap.ext fun a => h g a⟩
  infer_instance

open GroundTheory.ProfCoh in
theorem UpperTheory.Reformulated.B.Gua5.finite_cohomology_of_trivial_of_cyclic
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (n r : ℕ)
    (hC : ∀ (C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [IsDiscreteRep C] [Finite C.V] [IsAddCyclic C.V],
      (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) →
      Finite (cohomology C r))
    (A : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [IsDiscreteRep A] [Finite A.V]
    (htriv : ∀ (g : H) (a : A.V), A.ρ g a = a) (hn : ∀ a : A.V, n • a = 0) :
    Finite (cohomology A r) := by
  have hι : ∀ (B : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) [IsDiscreteRep B],
      (∀ m : ℕ, Function.Injective ((cochainsComplexι B).f m).hom) ∧
      ∀ (m : ℕ) (x : (Fin m → H) → B.V),
        (∃ y, ((cochainsComplexι B).f m).hom y = x) ↔ IsLocallyConstant x := by
    intro B _
    refine ⟨fun m => Subtype.val_injective, fun m x => ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩⟩
    rintro ⟨y, rfl⟩
    exact y.2
  refine UpperTheory.cyclic_trivial_induction n
    (fun B => ∀ [IsDiscreteRep B], Finite (cohomology B r))
    ?_ ?_ A ‹Finite A.V› htriv hn
  · intro C _ _ h1 h2 _
    exact hC C h1 h2
  · intro A B C f g hA hC' hf hfg hg PA PC _
    have := isDiscreteRep_of_forall_eq A hA
    have := isDiscreteRep_of_forall_eq C hC'
    obtain ⟨φ, ψ, w, hS⟩ := UpperTheory.cochain_injective_exact A B C f g _ _ _ (cochainsComplexι A)
      (cochainsComplexι B) (cochainsComplexι C) hf hfg hg
      (hι A).1 (hι B).1 (hι C).1 (hι A).2 (hι B).2 (hι C).2
    exact (UpperTheory.homology_finite_short_exact hS r).1 PA PC
