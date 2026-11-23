module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

theorem UpperTheory.Reformulated.B.Qi48.exists_psi :
    ∀ (L T : Type) [inst : Field L] [IsAlgClosed L] [inst_2 : CommRing T]
    [inst_3 : Algebra L T] [Algebra.FiniteType L T] (m : Ideal T),
    m.IsMaximal → ∃ (ψ : T →ₐ[L] L), ∀ (x : T), (ψ : T → L) x = (0 : L) ↔ x ∈ m := by
  intro L T _ _ _ _ _ m hm
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite L (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing L (T ⧸ m)
  have hb : Function.Bijective (Algebra.ofId L (T ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : L ≃ₐ[L] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId L (T ⧸ m)) hb
  refine ⟨(e.symm : (T ⧸ m) →ₐ[L] L).comp (Ideal.Quotient.mkₐ L m), fun x => ?_⟩
  change e.symm (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m
  rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
