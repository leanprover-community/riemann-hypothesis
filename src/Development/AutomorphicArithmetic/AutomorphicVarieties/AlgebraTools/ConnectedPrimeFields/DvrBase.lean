module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.dvrBase :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O], IsBase O := by
  intro O _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : Nontrivial (QuotSMulTop ϖ O) := by
    open Pointwise in
    refine Submodule.Quotient.nontrivial_iff.mpr ?_
    intro h
    have h1 : (1 : O) ∈ ϖ • (⊤ : Submodule O O) := by rw [h]; exact Submodule.mem_top
    obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one x (by simpa [smul_eq_mul] using hx))
  refine ⟨inferInstance, inferInstance, ⟨inferInstance, 1, ?_, [ϖ], rfl, ?_, ?_⟩, inferInstance⟩
  · rw [IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨fun a b hab => mul_left_cancel₀ hϖ.ne_zero (by simpa [smul_eq_mul] using hab), ?_⟩
    exact RingTheory.Sequence.IsRegular.nil _ _
