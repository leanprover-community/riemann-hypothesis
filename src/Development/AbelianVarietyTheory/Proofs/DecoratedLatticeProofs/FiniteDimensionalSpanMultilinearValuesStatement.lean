module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
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
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

-- Interpret the original scalar argument as the identity ring homomorphism.
local notation:max "MultilinearMap" R:max M:max N:max =>
  _root_.MultilinearMap (RingHom.id R) M N


theorem _root_.GlobalTheory.T.finiteDimensional_span_multilinear_values' : ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F) (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  letI : ∀ i, FiniteDimensional ℂ (W i) := hW
  let restricted : (∀ i, W i) →ₘₗ[ℂ] F := T.compLinearMap (fun i => (W i).subtype)
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (PiTensorProduct.lift restricted))
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ (fun i => ⟨v i, hv i⟩), ?_⟩
  rw [PiTensorProduct.lift.tprod]
  rfl
