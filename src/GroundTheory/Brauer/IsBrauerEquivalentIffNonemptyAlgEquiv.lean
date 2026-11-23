module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import GroundTheory.Brauer.TensorSimple
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
public import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct

universe u v w

section Azumaya

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]


omit [FiniteDimensional K A] in
variable (K A) in
theorem mulLeftRight_injective : Function.Injective (AlgHom.mulLeftRight K A) :=
  RingHom.injective (AlgHom.mulLeftRight K A).toRingHom


variable (K A) in
theorem mulLeftRight_bijective : Function.Bijective (AlgHom.mulLeftRight K A) := by
  refine ⟨mulLeftRight_injective K A, ?_⟩
  have h := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight K A).toLinearMap)
    (by rw [Module.finrank_tensorProduct, MulOpposite.finrank, Module.finrank_linearMap])
  exact h.mp (mulLeftRight_injective K A)


end Azumaya

section Equivalence

variable {K : Type u} [Field K]


end Equivalence

section Group

variable (K : Type u) [Field K]

variable {K}

end Group

section DivisionPart

variable {K : Type u} [Field K]

section ColumnIdeal

variable {R : Type v} [Ring R] [Algebra K R] {D : Type w} [DivisionRing D] [Algebra K D]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (e : R ≃ₐ[K] Matrix ι ι D) (i₀ : ι)

end ColumnIdeal

end DivisionPart

end GroundTheory.Brauer
