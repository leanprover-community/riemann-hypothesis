module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem span_adjoin_gen_eq_top {K : UQ} (B : InvAlg K) (hP : B.P.Separable) :
    Submodule.span K.E ((Subalgebra.toSubmodule (Algebra.adjoin K.O {B.g}) : Submodule K.O B.A) : Set B.A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, rfl⟩ := Sandwich.exists_aeval B hP x
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show B.g ^ i ∈ Algebra.adjoin K.O {B.g}
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i

theorem pow_smul_mem_adjoin_gen : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  intro K B a hP ha
  obtain ⟨m, hm⟩ := Sandwich.integral_sub B hP a ha.2.1 _ (span_adjoin_gen_eq_top B hP)
  refine ⟨m, fun r hr => ?_⟩
  have h := hm m le_rfl r hr
  have e : (al K a ^ m) • r = algebraMap K.O B.A a ^ m * r := by
    rw [Algebra.smul_def, al, ← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply]
  rw [e]
  exact h

end GlobalTheory.UnitLemma.Desc
