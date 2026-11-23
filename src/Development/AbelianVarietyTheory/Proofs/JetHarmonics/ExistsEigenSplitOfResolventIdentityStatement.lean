module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentity
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
import Formalism.RealPlaceAnalysis.StatementA

@[expose] public section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.exists_eigenSplit_of_resolventIdentity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  first | exact @GlobalTheory.exists_sum_eigen_split_of_resolvent | exact GlobalTheory.exists_sum_eigen_split_of_resolvent | (intros; apply GlobalTheory.exists_sum_eigen_split_of_resolvent <;> assumption)
