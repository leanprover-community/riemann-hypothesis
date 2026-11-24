module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Topology Matrix

namespace GlobalTheory.CuspRep.ContAut

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_map_pFin :
    Continuous (GeneralLinearGroup.map (pFin E) : GA E a → GL (Fin a) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pFin E))

theorem continuous_map_pInf :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf E))

theorem continuous_of_isOpen_stab : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsOpen {k | finRep E a k φ = φ} → Continuous φ.1 := by
  intro E _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA E a => g⁻¹ * x := continuous_const.mul continuous_id
  have h1 : Continuous fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((continuous_map_pInf E a).comp hm)
  have h2 : ContinuousAt (fun x : GA E a => chart φ.1 g (toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA E a => toL (GeneralLinearGroup.map (pInf E) (g⁻¹ * x)).val)
      (contDiffAt_chart φ.2 g (val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA E a | finRep E a (GeneralLinearGroup.map (pFin E) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage ((continuous_map_pFin E a).comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * infGL E a _ * finGL E a _) = _
  rw [mul_assoc, infGL_mul_finGL, mul_inv_cancel_left]

end GlobalTheory.CuspRep.ContAut
