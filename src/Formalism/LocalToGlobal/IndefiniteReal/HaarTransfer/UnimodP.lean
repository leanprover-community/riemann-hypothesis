module

public import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.Unimod
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
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

namespace Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory

theorem prodStatement_holds : HaarRightInvProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ μ hμ
  have : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  have : (Measure.haar : Measure G₂).IsMulRightInvariant := h₂ _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂))]
  infer_instance

theorem piStatement_holds : HaarRightInvPi := by
  intro ι _ G _ _ _ _ _ _ _ _ h μ hμ
  have : ∀ i, (Measure.haar : Measure (G i)).IsMulRightInvariant := fun i => h i _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ (Measure.pi fun i => (Measure.haar : Measure (G i)))]
  infer_instance

theorem transferStatement_holds : HaarRightInvTransfer := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ e h ν hν
  have hμ : (ν.map e.symm).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν e.symm
  have hr : (ν.map e.symm).IsMulRightInvariant := h _ hμ
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hν' : ν = (ν.map e.symm).map e := by
    rw [Measure.map_map he hes]
    have : (e : G → H) ∘ e.symm = id := funext fun x => e.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  rw [hν', Measure.map_map (measurable_mul_const g) he]
  have hc : (fun x => x * g) ∘ (e : G → H) = (e : G → H) ∘ (fun x => x * e.symm g) := by
    funext x; simp [map_mul]
  rw [hc, ← Measure.map_map he (measurable_mul_const _), hr.map_mul_right_eq_self (e.symm g)]

end Formalism.IndefR.Leaf.Proofs
