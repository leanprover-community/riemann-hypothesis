module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
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
import Mathlib.RingTheory.Finiteness.Lattice
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

@[expose] public section

open Formalism.MainNotions.S

namespace GlobalTheory.IrrAdm

theorem isIrrAdm_of_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  intro n ε H _ _ _ _ π hU hI
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖π k v‖ = ‖v‖ := fun k hk v =>
    hU.2.1 k (GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk) v
  refine ⟨inferInstance, ⟨hU.1, hU.2.2, hK, ?_⟩, hI⟩
  intro Λ
  classical
  by_cases hne : ∃ S₀ : Submodule ℂ H, S₀ ≤ ⊤ ∧ IsKTypeOf ε π Λ S₀
  · obtain ⟨S₀, -, hS₀⟩ := hne
    haveI : FiniteDimensional ℂ S₀ := hS₀.1
    have hY := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε H π hU hI).1 S₀ hS₀.1 hS₀.2.1
    let b := Module.finBasis ℂ S₀
    choose Y hYf hvY hYB using fun i => hY (b i) (b i).2
    haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYf
    refine Submodule.finiteDimensional_of_le (sSup_le fun S hS => ?_) (S₂ := ⨆ i, Y i)
    obtain ⟨B, hB, rfl⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H π hU.1 hU.2.2 hK).2 Λ S₀ S hS₀ hS.2
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    have hx' : (⟨x, hx⟩ : S₀) ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span S₀.subtype hx'
    rw [← Set.range_comp] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨i, rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, Function.comp_apply, Submodule.subtype_apply,
      SetLike.mem_coe]
    exact Submodule.mem_iSup_of_mem i (hYB i B hB _ (hvY i))
  · have : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S} = ∅ :=
      Set.eq_empty_of_forall_notMem fun S hS => hne ⟨S, hS⟩
    rw [this, sSup_empty]
    infer_instance

end GlobalTheory.IrrAdm
