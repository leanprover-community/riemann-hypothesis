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

noncomputable section

open NumberField Topology

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem IsAutForm.continuous {φ : Sm E a} (h : IsAutForm φ) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hmul : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ := by
    refine (h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_
    simp
  have heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
    filter_upwards [hN] with g hg
    rw [chart_val]
    have hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x :=
      fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg
    conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt
  exact ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc
    (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt

end GlobalTheory.CuspRep
