module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FGNullstellensatz.proof : FGNullstellensatz.Statement := by
  intro F _ D _ _ _ _ r hr
  have hJ : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := F)
  have hmem : r ∈ (⊥ : Ideal D).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    let _ : Field (D ⧸ m) := Ideal.Quotient.field m
    have : Algebra.FiniteType F (D ⧸ m) := inferInstance
    have : Module.Finite F (D ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (D ⧸ m)
    have : Algebra.IsAlgebraic F (D ⧸ m) := inferInstance
    let ψ : (D ⧸ m) →ₐ[F] AlgebraicClosure F := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h0 : ψ (Ideal.Quotient.mkₐ F m r) = 0 := hr (ψ.comp (Ideal.Quotient.mkₐ F m))
    have h1 : Ideal.Quotient.mkₐ F m r = 0 := (map_eq_zero_iff ψ ψ.toRingHom.injective).mp h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  rw [← Ideal.radical_eq_jacobson] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact IsReduced.eq_zero r ⟨k, by simpa using hk⟩

end GroundTheory.Heights₂.Heights
