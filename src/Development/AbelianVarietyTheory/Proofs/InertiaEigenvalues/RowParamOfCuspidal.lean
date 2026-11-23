module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem rowParam_of_cuspParam : ∀ (D : D7) (Rw : RowSide D), GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ) → (∀ k v, IsSplitPl D.host (D.naut.plGw k v)) → RowParam D Rw := by
  intro D Rw hP hC hS j hj1 hj2 σ hσ hg
  obtain ⟨π, h⟩ := hP j hj1 hj2 σ hσ hg
  have hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true := fun τ => by
    ext x
    have e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x) :=
      D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x
    rw [e]
    rfl
  have hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) := by
    intro τ
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def]
  refine ⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩
  · obtain ⟨a, b⟩ := h.2.2.2.2.2 τ
    refine ⟨?_, ?_⟩
    · rw [← hpar]; exact a
    · rw [← hembb, b, hpar, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp
  · rw [Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]
end GlobalTheory.TwInputs
