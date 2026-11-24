module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorSumAnnihilator
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

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.tensor_sum_annihilator : ∀ {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ), ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KillSum.sum_killed | exact GlobalTheory.CompanionTheory.KillSum.sum_killed | (intros; apply GlobalTheory.CompanionTheory.KillSum.sum_killed <;> assumption)
