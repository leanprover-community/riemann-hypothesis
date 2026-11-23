module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc.JumpBlock

theorem reflS_blockJ_iff (D : D7) (q : ℚ) :
    AdmissibleParameterJ.refl D q ∈ AdmissibleParameterJ.blockJ D ↔ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  simp only [AdmissibleParameterJ.refl, AdmissibleParameterJ.blockJ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith

theorem jumps_iff : ∀ (D : D7) (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) (q : ℚ),
    q ∈ AdmissibleParameterJ.JJ D up j ρ ↔ q ∈ AdmissibleParameterJ.JW D up j ρ ∨ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  intro D up j ρ q
  cases up
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jm, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.reflS,
      Set.mem_union, Set.mem_setOf_eq, Bool.false_eq_true, if_false]
    rw [reflS_blockJ_iff]
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.blockJ,
      Set.mem_union, Set.mem_setOf_eq, if_true]

end GlobalTheory.UseLoc.JumpBlock
