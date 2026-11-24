module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddFinrankLeFinrankInfComapSubId
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

open TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | exact GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | (intros; apply GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id <;> assumption)
