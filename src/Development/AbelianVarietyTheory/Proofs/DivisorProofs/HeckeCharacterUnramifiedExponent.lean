module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

noncomputable section

namespace GlobalTheory.BotLValue

section General

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

end General

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open Formalism.L2.Host (aboveF)

open NumberField IsDedekindDomain in
private theorem eq_or_eq_of_comp_eq_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2) (ψ : F →+* ℂ)
    (ρ α β : E →+* ℂ) (hρ : ρ.comp (algebraMap F E) = ψ) (hα : α.comp (algebraMap F E) = ψ)
    (hβ : β.comp (algebraMap F E) = ψ) (hαβ : α ≠ β) : ρ = α ∨ ρ = β := by
  classical
  letI : Algebra F ℂ := ψ.toAlgebra
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let mk : ∀ γ : E →+* ℂ, γ.comp (algebraMap F E) = ψ → E →ₐ[F] ℂ := fun γ hγ =>
    { toRingHom := γ
      commutes' := fun a => (congrArg (fun f : F →+* ℂ => f a) hγ : _) }
  have hcoe : ∀ (γ : E →+* ℂ) (hγ : γ.comp (algebraMap F E) = ψ), ((mk γ hγ : E →ₐ[F] ℂ) : E →+* ℂ) = γ :=
    fun γ hγ => rfl
  by_contra hne
  push_neg at hne
  have hcard := AlgHom.card F E ℂ
  rw [h2] at hcard
  have hfa : mk ρ hρ ≠ mk α hα := fun e => hne.1 (by rw [← hcoe ρ hρ, ← hcoe α hα, e])
  have hfb : mk ρ hρ ≠ mk β hβ := fun e => hne.2 (by rw [← hcoe ρ hρ, ← hcoe β hβ, e])
  have hab : mk α hα ≠ mk β hβ := fun e => hαβ (by rw [← hcoe α hα, ← hcoe β hβ, e])
  have h3 : ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfa, hfb]), Finset.card_pair hab]
  have := Finset.card_le_univ ({mk ρ hρ, mk α hα, mk β hβ} : Finset (E →ₐ[F] ℂ))
  omega


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.BotLValue.isCMType_embOver {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, _root_.GlobalTheory.AdelicU.EmbOver E w) :
    _root_.GlobalTheory.CMVal.IsCMType fun w => (τ w).1 := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at h
  obtain ⟨hF, hE, h2, hσ⟩ := h
  unfold _root_.GlobalTheory.CMVal.IsCMType
  have hreal : ∀ v : InfinitePlace F, ComplexEmbedding.conjugate v.embedding = v.embedding :=
    fun v => ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp (hF.isReal v))
  have hconj : ∀ (v : InfinitePlace F) (γ : E →+* ℂ), γ.comp (algebraMap F E) = v.embedding →
      (ComplexEmbedding.conjugate γ).comp (algebraMap F E) = v.embedding := by
    intro v γ hγ
    rw [← hreal v, ← hγ]
    rfl
  have hτ : ∀ v : InfinitePlace F, ((τ v).1).comp (algebraMap F E) = v.embedding := fun v => (τ v).2
  have hne : ∀ v : InfinitePlace F, (τ v).1 ≠ ComplexEmbedding.conjugate (τ v).1 := by
    intro v e
    have hc := hE.isComplex (InfinitePlace.mk (τ v).1)
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff] at hc
    exact hc e.symm
  intro ρ
  set v := InfinitePlace.mk (ρ.comp (algebraMap F E)) with hvdef
  have hv : ρ.comp (algebraMap F E) = v.embedding := by
    rcases InfinitePlace.embedding_mk_eq (ρ.comp (algebraMap F E)) with e | e
    · exact e.symm
    · rw [← hreal v, e]
      exact (star_star _).symm
  refine ⟨v, eq_or_eq_of_comp_eq_of_finrank_two h2 v.embedding ρ _ _ hv (hτ v) (hconj v _ (hτ v)) (hne v), ?_⟩
  intro w hw
  have hw' : ρ.comp (algebraMap F E) = w.embedding := by
    rcases hw with e | e
    · rw [e]; exact hτ w
    · rw [e]; exact hconj w _ (hτ w)
  rw [hvdef, hw', InfinitePlace.mk_embedding]

end GlobalTheory.BotLValue

end
