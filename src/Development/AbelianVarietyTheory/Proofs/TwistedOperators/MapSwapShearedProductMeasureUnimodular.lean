module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem map_swap_map_shear (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H) (hNc : IsClosed (N : Set H))
    (κ : Measure N) (hκ : κ.IsHaarMeasure) (hinv : κ.map (fun n => n⁻¹) = κ) :
    ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap
      = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI := hκ
  have hsh : Measurable (shear N) := (measurableEmbedding_shear hNc).measurable
  have hT : MeasurePreserving (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) (κ.prod ν) (κ.prod ν) := by
    refine MeasurePreserving.skew_product (f := fun n : N => n⁻¹) (g := fun (n : N) (h : H) => (n : H) * h)
      ⟨measurable_inv, hinv⟩ ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun n => (measurePreserving_mul_left ν (n : H)).map_eq
  have hcomm : Prod.swap ∘ shear N = shear N ∘ (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) := by
    funext p
    simp [shear]
  rw [Measure.map_map measurable_swap hsh, hcomm, ← Measure.map_map hsh hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
