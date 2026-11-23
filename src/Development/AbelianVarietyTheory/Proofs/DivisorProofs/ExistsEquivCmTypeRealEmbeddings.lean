module

public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.CMTypeEmb

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) : Fintype.card I = Module.finrank ℚ (FR E) := by
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)
  have hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E)) :=
    Fintype.card_congr (IsCMField.equivInfinitePlace E)
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (FR E)
  have hr : InfinitePlace.nrComplexPlaces (FR E) = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (FR E)
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)
  omega

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  intro E _ _ _ I _ φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := card_eq_finrank hφ
  let e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀
  refine ⟨e₀.symm.trans e, fun i x ↦ ?_⟩
  have := he (e₀.symm i) x
  simp only [Equiv.apply_symm_apply] at this
  simp only [Equiv.trans_apply]
  exact this.symm

end GlobalTheory.CMTypeEmb
