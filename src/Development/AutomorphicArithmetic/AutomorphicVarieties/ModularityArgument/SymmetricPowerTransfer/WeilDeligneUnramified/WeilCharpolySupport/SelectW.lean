module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem selectThrough {α β : Type} (f : α → β) (S : Set α) (a : α) (ha : a ∈ S) :
    ∃ P ⊆ S, a ∈ P ∧ Set.InjOn f P ∧ ∀ w ∈ S, ∃ w' ∈ P, f w' = f w := by
  classical
  haveI : Nonempty α := ⟨a⟩
  let g : β → α := fun b => if b = f a then a else Function.invFunOn f S b
  have hg : ∀ b ∈ f '' S, g b ∈ S ∧ f (g b) = b := by
    intro b hb
    by_cases h : b = f a
    · simp only [g, if_pos h]
      exact ⟨ha, h.symm⟩
    · simp only [g, if_neg h]
      exact ⟨Function.invFunOn_mem hb, Function.invFunOn_eq hb⟩
  refine ⟨g '' (f '' S), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact (hg b hb).1
  · exact ⟨f a, ⟨a, ha, rfl⟩, by simp [g]⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ h
    rw [(hg b hb).2, (hg c hc).2] at h
    rw [h]
  · intro w hw
    exact ⟨g (f w), ⟨f w, ⟨w, hw, rfl⟩, rfl⟩, (hg _ ⟨w, hw, rfl⟩).2⟩

theorem UpperTheory.V.Z.Sym.W.selectW :
    UpperTheory.V.Z.Sym.W.SelectW := by
  intro L _ _ _ X w₀ hw₀
  exact selectThrough _ X w₀ hw₀
