module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSsIdxInjective
import Formalism.GradedWeylDivisibility.FinalD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem finrank_nablaSq_eq_card (K : Type) [Field K] (N : ℕ) (lam : DomWeight N) :
    Module.finrank K (nablaSq K N lam) = Nat.card (ssIdx N N lam.natW) := by
  obtain ⟨b, ⟨hli, hb, -⟩, -⟩ := sSBasis K N N lam.natW
  have : Finite (ssIdx N N lam.natW) := (sSIdxFinite N N _).to_subtype
  have := Fintype.ofFinite (ssIdx N N lam.natW)
  unfold nablaSq
  rw [← hb, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

theorem finrank_le_finrank_directSum_below (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    Module.finrank ℂ (nablaSq ℂ N lam) ≤ Module.finrank ℂ (⨁ mu : Below h lam, nablaSq ℂ n mu.1) := by
  obtain ⟨F, hF⟩ := GlobalTheory.Branching.exists_ssIdx_injective n N h lam
  have := Fintype.ofFinite (Below h lam)
  have : ∀ mu : Below h lam, Finite (ssIdx n n mu.1.natW) := fun mu => (sSIdxFinite n n _).to_subtype
  rw [Module.finrank_directSum, finrank_nablaSq_eq_card]
  simp only [finrank_nablaSq_eq_card]
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective F hF

end GlobalTheory.Branching
