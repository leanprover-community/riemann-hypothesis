module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt
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

open NumberField

namespace PI.IdealLatticeWork

theorem idealBasis : IdealBasis := by
  intro K _ _ b cc hcc
  classical
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨(bI 0 : 𝓞 K), (bI 0).2, (bI 1 : 𝓞 K), (bI 1).2, ?_, ?_⟩
  · intro c hc
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h := congrArg Subtype.val (bI.sum_repr ⟨c, hc⟩)
    rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower] at h
    exact h.symm
  · refine ⟨b.repr (bI 0) 0, b.repr (bI 0) 1, b.repr (bI 1) 0, b.repr (bI 1) 1, ?_, ?_, ?_⟩
    · have h := b.sum_repr (bI 0 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := b.sum_repr (bI 1 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := Ideal.natAbs_det_basis_change b cc bI
      rw [Module.Basis.det_apply, Matrix.det_fin_two] at h
      simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at h
      rw [← h]
      congr 1
      ring

end PI.IdealLatticeWork
