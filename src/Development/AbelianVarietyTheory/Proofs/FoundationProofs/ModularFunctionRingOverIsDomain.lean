module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIffStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem ring_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  intro E
  haveI : Nontrivial (GlobalTheory.FN.ring E) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) UpperHalfPlane.I) h
    simp at h1
  haveI : NoZeroDivisors (GlobalTheory.FN.ring E) := by
    refine ⟨fun {a b} hab => ?_⟩
    have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1
    have ha := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E a ((hmem a).1 a.2)
    have hb := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E b ((hmem b).1 b.2)
    have h0 : ∀ τ, (a : ℍ → ℂ) τ * (b : ℍ → ℂ) τ = 0 := by
      intro τ
      have := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) τ) hab
      simpa using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff a b ha hb h0 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FN
