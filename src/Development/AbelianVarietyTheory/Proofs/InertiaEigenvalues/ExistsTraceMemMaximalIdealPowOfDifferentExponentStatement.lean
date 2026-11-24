module

public import GroundTheory.LocalFields.Different
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceMemMaximalIdealPowOfDifferentExponent
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_trace_mem_maximalIdeal_pow_of_differentExponent : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | exact GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent | (intros; apply GlobalTheory.PMon.Ram.exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent <;> assumption)
