module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.IrrQuot

theorem main : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  intro G V _ _ _ ρ s hV hspan
  have key : ∀ T : Subrepresentation ρ, (∀ v ∈ s, v ∈ T.toSubmodule) → T = ⊤ := by
    intro T hT
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro w ⟨g, v, hv, rfl⟩
    exact T.apply_mem_toSubmodule g (hT v hv)
  haveI : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule := by
    let t : Finset ρ.asModule := s
    refine ⟨⟨t, ?_⟩⟩
    have h := key (Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)))
      (fun v hv => Submodule.subset_span (R := MonoidAlgebra ℂ G) (s := (t : Set ρ.asModule)) hv)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)) := by
      rw [h]; trivial
    exact hx
  haveI : IsCoatomic (Subrepresentation ρ) :=
    (OrderIso.isCoatomic_iff Subrepresentation.subrepresentationSubmoduleOrderIso).2 inferInstance
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at this
    exact hv this
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot ⊤ M, GlobalTheory.SmGL.isIrreducible_subQuot hM.covBy_top, ?_⟩
  refine ⟨⟨(Submodule.mkQ _).comp (LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial)), fun g => rfl⟩, ?_⟩
  intro y
  obtain ⟨⟨v, _⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

end GlobalTheory.IrrQuot
