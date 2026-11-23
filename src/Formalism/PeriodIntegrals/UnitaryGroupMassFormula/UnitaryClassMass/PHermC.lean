module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermSk
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem wPlace : WPlace := by
  intro F E _ _ _ _ _ p hp h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField E)
    (Ideal.eq_bot_of_comap_eq_bot h)

theorem bcU : BcU := by
  intro F E _ _ _ σ M J R _ _ g hg
  have key : ∀ A : Matrix (Fin M) (Fin M) E,
      PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ R)
          (A.map (PI.UnitaryApproxDefs.inclE (F := F) R)) =
        (PI.UnitaryApproxDefs.cT (σ : E →+* E) A).map (PI.UnitaryApproxDefs.inclE (F := F) R) := by
    intro A
    ext i j
    simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]
  have hg' : PI.UnitaryApproxDefs.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
      (g : Matrix (Fin M) (Fin M) E) = J := hg
  change PI.UnitaryApproxDefs.cT _ _ * _ * _ = _
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.mapMatrix_apply]
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem gramOK : GramOK := by
  intro F E _ _ _ _ σ hσ V _ _ _ h M b hsy hnd
  refine ⟨?_, ?_⟩
  · unfold PI.UnitaryApproxDefs.IsHerm PI.UnitaryApproxDefs.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, AlgHom.coe_toRingHom, hσ, gramOf]
    rw [← starRingEnd_apply]
    exact hsy.eq (b j) (b i)
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hc0
    have hbw : ∀ i, h (b i) (∑ j, c j • b j) = 0 := by
      intro i
      have hi := congrFun hc i
      simp only [Matrix.mulVec, dotProduct, gramOf, Pi.zero_apply] at hi

      simp only [map_sum, map_smul, smul_eq_mul]
      rw [← hi]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hw : ∀ x, h x (∑ j, c j • b j) = 0 := by
      intro x
      generalize hwd : (∑ j, c j • b j) = w at hbw ⊢
      rw [← b.sum_repr x]

      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbw, smul_zero,
      Finset.sum_const_zero]
    have hw0 := hnd.2 _ hw
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c hw0 j

end PI.UnitaryGroupMassFormula.UJClassMass

end
