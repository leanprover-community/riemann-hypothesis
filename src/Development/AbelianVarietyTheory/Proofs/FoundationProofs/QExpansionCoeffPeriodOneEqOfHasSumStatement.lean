module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ), (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ n, GlobalTheory.Hk.coef f n = a n := by
  first | exact @GlobalTheory.Hk.coef_of_hasSum | exact GlobalTheory.Hk.coef_of_hasSum | (intros; apply GlobalTheory.Hk.coef_of_hasSum <;> assumption)
