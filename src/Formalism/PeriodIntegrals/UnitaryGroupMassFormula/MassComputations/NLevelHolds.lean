module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

theorem nLevel_holds : NLevel := by
  intro D X u y hyN hyK
  obtain ⟨c, hc, hec, hfc, hzc⟩ := mults X u
  have hxK := X.xu_K u
  have hxiK : (X.xu u)⁻¹ ∈ X.B.I.Kset := Kset_inv hxK
  have hκK : (X.xu u)⁻¹ * y * X.xu u ∈ X.B.I.Kset := Kset_mul (Kset_mul hxiK hyK) hxK
  have hAiA := fmat_inv_mul (X.xu u)
  have hT : ∀ v, (X.B.I.fmat ((X.xu u)⁻¹ * y * X.xu u) - 1) *ᵥ v =
      Tm (X.B.I.fmat (X.xu u)⁻¹) (X.B.I.fmat y) (X.B.I.fmat (X.xu u)) v := by
    intro v
    show (X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat y * X.B.I.fmat (X.xu u) - 1) *ᵥ v = _
    simp only [Tm, sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [sub_mul, one_mul, mul_sub, hAiA, sub_mulVec, one_mulVec]
  have hN : y ∈ Nfin X.B.I X.eR (X.zR u) := hyN
  have hcore := core X hc hec hfc (Kset_Lf hxK) (Kset_Lf hxiK) (Kset_Lf hyK) hAiA (fmat_mul_inv (X.xu u))
    (hA_fmat X.B.I (X.xu u)) (fun a => (X.xu_fix u a).1) hN.1 (incl X.B.I (X.zR u)) hN.2.1 hN.2.2 hzc
  refine ⟨hκK, ?_⟩
  unfold K2cong
  simp only [hT]
  exact hcore

end MassDataMassesW.NLev
