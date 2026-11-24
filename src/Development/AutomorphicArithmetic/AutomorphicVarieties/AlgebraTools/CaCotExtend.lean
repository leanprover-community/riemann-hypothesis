module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
public import Mathlib.Algebra.Module.SpanRankOperations
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_extend :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∃ (s : ℕ) (y : Fin s → R), CotInd R (Sum.elim x y) ∧
        Ideal.span (Set.range (Sum.elim x y)) = maximalIdeal R ∧
        Fintype.card κ + s = (maximalIdeal R).spanFinrank := by
  intro R _ _ _ κ _ x hx
  obtain ⟨hm, hli⟩ := (cotInd_iff R x).mp hx
  set v : κ → CotangentSpace R := fun k => (maximalIdeal R).toCotangent ⟨x k, hm k⟩ with hv
  let bW := Module.Basis.span hli
  let bQ := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ Submodule.span (ResidueField R) (Set.range v))
  let B := Module.Basis.sumQuot bW bQ
  choose z hz using fun i => (maximalIdeal R).toCotangent_surjective (B (Sum.inr i))
  refine ⟨_, fun i => (z i : R), ?_⟩
  have hmem : ∀ j, Sum.elim x (fun i => (z i : R)) j ∈ maximalIdeal R := by
    rintro (k | i)
    · exact hm k
    · exact (z i).2
  have hB : (fun j => (maximalIdeal R).toCotangent ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩) = ⇑B := by
    funext j
    rcases j with k | i
    · simp [B, bW, Module.Basis.span_apply, hv]
    · simpa using hz i
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  refine ⟨(cotInd_iff R _).mpr ⟨hmem, ?_⟩, ?_, ?_⟩
  · rw [hB]
    exact B.linearIndependent
  · let g : κ ⊕ Fin _ → maximalIdeal R := fun j => ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩
    have hspan : Submodule.span R (Set.range g) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
      have : (maximalIdeal R).toCotangent ∘ g = ⇑B := hB
      rw [this, B.span_eq]
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank_eq_card_basis B,
      Fintype.card_sum, Fintype.card_fin]
