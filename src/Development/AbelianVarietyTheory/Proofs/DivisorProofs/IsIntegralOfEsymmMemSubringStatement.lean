module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubring
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.isIntegral_of_esymm_mem_subring : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by
  first | exact @GlobalTheory.QFam.isIntegral_of_esymm_mem | exact GlobalTheory.QFam.isIntegral_of_esymm_mem | (intros; apply GlobalTheory.QFam.isIntegral_of_esymm_mem <;> assumption)
