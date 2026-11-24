module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LeviMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  PI.UnitaryDimensionFormula.unitaryCongruence

namespace PI.UnitaryDimensionFormula.NormCutK

section LeviMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem resT_of_mem (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E) :
    resT TR v z = TR.res v ⟨z, hz⟩ := by
  unfold resT; rw [dite_eq_left hz]

theorem res_eq_zero_of_Z (v : TR.Pl) {z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hz : z ∈ IntAf X.B.I.F X.B.I.E)
    (hZ : ZMod' X.B.I X.B.g z) : TR.res v ⟨z, hz⟩ = 0 :=
  (TR.res_ker ⟨z, hz⟩).2 (Z_smul X.B.I X.B.g X.ew_int hZ) v

def PhiSub (x : X.B.I.Gf) (i : Fin D.R.k) : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {z | ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
    ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z)}
  add_mem' {z w} hz hw := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ (z + w)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) (z + w) =
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) +
        (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ w) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) w) := by
      simp only [Matrix.mulVec_add, hA_add_right, mul_add, Finset.sum_add_distrib]; ring
    rw [e]; exact Z_add X.B.I X.B.g hz hw
  zero_mem' := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ 0) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) 0)
    have h0 : ∀ u : VA X.B.I, hA X.B.I u 0 = 0 := fun u => (hL X.B.I u).map_zero
    simp only [Matrix.mulVec_zero, h0, mul_zero, Finset.sum_const_zero, sub_zero]
    exact Z_zero X.B.I X.B.g
  smul_mem' c z hz := by
    show ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
      ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z))
    have e : hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z)) -
        ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ z) -
          ∑ l, hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw l) * hA X.B.I (X.bwd l) z) := by
      simp only [Matrix.mulVec_smul, hA_smul_right, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]; exact Z_smul X.B.I X.B.g c.2 hz

theorem dual_beta_reference_congruence (i : Fin D.R.k) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a)) := by
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral i).2.2 a).2.2.1

theorem leviM_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset)
    (hyb : ∀ j, X.B.I.fmat y *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0 ∪ Set.range X.bw))
    (hxe : ∀ a, X.B.I.fmat x *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (Set.range X.e0)) (v : TR.Pl) :
    leviM TR (x * y) v = leviM TR x v * leviM TR y v := by
  apply Formalism.L2.SG.NormCut.leviM_mul <;> assumption

end LeviMul

end PI.UnitaryDimensionFormula.NormCutK
