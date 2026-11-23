module

public import Formalism.LocalRingCardinality.DataSpaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree

@[expose] public section

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc


variable {E : Type} [Field E] [NumberField E]



variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions


section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem hT_equivFun_symm (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i : Fin S.rank)
    (z : Fin S.rank → E) :
    S.hT (b i) (b.equivFun.symm z) = ((fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ z) i := by

  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gram_det_ne (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) :
    Matrix.det (fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hy0 : b.equivFun.symm z ≠ 0 := by
    intro h
    apply hz
    have := b.equivFun.apply_symm_apply z
    rw [h, map_zero] at this
    exact this.symm
  apply hy0
  apply S.nondeg.2
  intro x

  rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_equivFun_symm, hGz]
  simp

end Coord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
