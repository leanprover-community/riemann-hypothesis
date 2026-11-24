module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace UpperTheory.NonzeroTypeTheory

namespace TranslationCoordinates

variable {K : Type} [Group K] (W : Submodule ℂ (K → ℂ))
  (hW : ∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W)

def rW : Representation ℂ K W := sub (rightReg ℂ K ℂ) W (fun k φ hφ => hW φ hφ k)

def coord {m : ℕ} (c : W ≃ₗ[ℂ] (Fin m → ℂ)) : Representation ℂ K (Fin m → ℂ) where
  toFun k := c.toLinearMap ∘ₗ rW W hW k ∘ₗ c.symm.toLinearMap
  map_one' := by ext v i; simp
  map_mul' a b := by ext v i; simp [map_mul]

end TranslationCoordinates

theorem finiteDimensionalTranslation_holds : FiniteDimensionalTranslationCoordinates := by
  intro K _ _ W hfin hW hsm
  have := hfin
  let c := (Module.finBasis ℂ W).equivFun
  let V0 := TranslationCoordinates.coord W hW c
  let e : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (K → ℂ) := W.subtype ∘ₗ c.symm.toLinearMap
  have he : ∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v) := by
    intro k v
    simp [e, V0, TranslationCoordinates.coord, TranslationCoordinates.rW, sub]
  have hinj : Function.Injective e := W.injective_subtype.comp c.symm.injective
  refine ⟨_, V0, e, hinj, ?_, he, ?_⟩
  · ext φ
    constructor
    · rintro ⟨v, rfl⟩
      simp [e]
    · intro hφ
      exact ⟨c ⟨φ, hφ⟩, by simp [e]⟩
  · intro v
    have hset : {g : K | V0 g v = v} = {g : K | rightReg ℂ K ℂ g (e v) = e v} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      rw [← he]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hsm _ (by simp [e])

end UpperTheory.NonzeroTypeTheory
