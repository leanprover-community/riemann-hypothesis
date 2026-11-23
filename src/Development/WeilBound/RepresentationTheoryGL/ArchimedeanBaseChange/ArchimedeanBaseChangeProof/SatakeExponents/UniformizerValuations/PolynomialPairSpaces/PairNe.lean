module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InfParts
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd.PairSpaceNonzero

theorem pairSpace_left_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₂ : Submodule ℂ (Sm E b)) : pairSpace (⊥ : Submodule ℂ (Sm E a)) U₂ = ⊥ := by
  unfold pairSpace
  rw [Submodule.span_eq_bot]
  rintro F ⟨φ₁, h₁, φ₂, -, rfl⟩
  rw [Submodule.mem_bot] at h₁
  subst h₁
  funext x
  simp

theorem pairSpace_right_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) : pairSpace U₁ (⊥ : Submodule ℂ (Sm E b)) = ⊥ := by
  unfold pairSpace
  rw [Submodule.span_eq_bot]
  rintro F ⟨φ₁, -, φ₂, h₂, rfl⟩
  rw [Submodule.mem_bot] at h₂
  subst h₂
  funext x
  simp

end PositivityTheory.Rg.BcB.F.LemDd.PairSpaceNonzero

namespace PositivityTheory.Rg.BcB.F.LemDd

theorem PairNe_holds : PairNe := by
  intro E _ _ _ a b U₁ U₂ G hG hne
  refine ⟨fun h => hne ?_, fun h => hne ?_⟩
  · subst h
    rw [PairSpaceNonzero.pairSpace_left_bot, Submodule.mem_bot] at hG
    exact hG
  · subst h
    rw [PairSpaceNonzero.pairSpace_right_bot, Submodule.mem_bot] at hG
    exact hG

end PositivityTheory.Rg.BcB.F.LemDd

end
