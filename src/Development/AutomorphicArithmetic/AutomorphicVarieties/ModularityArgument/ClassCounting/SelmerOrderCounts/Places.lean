module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

@[expose] public section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.places :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsTotallyComplex F ∧ Fintype.card (InfinitePlace F) = orderOf γ * InfinitePlace.nrComplexPlaces L ∧ ∀ (k : ℕ) (w : InfinitePlace F), γ ^ k • w = w ↔ orderOf γ ∣ k := by
  intro L F _ _ _ _ _ γ hL hG hγ
  haveI := hL
  haveI : IsTotallyComplex F := isTotallyComplex_of_algebra L F
  haveI : IsUnramifiedAtInfinitePlaces L F :=
    ⟨fun w => InfinitePlace.isUnramified_iff.mpr (Or.inr (IsTotallyComplex.isComplex _))⟩
  have htop : Subgroup.zpowers γ = ⊤ := eq_top_iff.mpr fun σ _ => hγ σ
  have hcard : Module.finrank L F = orderOf γ := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_zpowers, htop, Subgroup.card_top]
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [IsUnramifiedAtInfinitePlaces.card_infinitePlace L F, hcard,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, mul_comm]
  · intro k w
    have hst := (InfinitePlace.isUnramified L w).stabilizer_eq_bot
    rw [orderOf_dvd_iff_pow_eq_one, ← MulAction.mem_stabilizer_iff, hst, Subgroup.mem_bot]
