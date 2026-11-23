module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev

@[expose] public section

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

end GlobalTheory.IdxAll
