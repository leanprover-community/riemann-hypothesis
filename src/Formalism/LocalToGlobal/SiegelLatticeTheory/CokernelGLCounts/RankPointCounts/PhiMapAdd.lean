module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section Covol

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]

def phiMap (x : mixedSpace K) : ι → ℂ := fun i => if cj i then (starRingEnd ℂ) (x.2 (σ i)) else x.2 (σ i)

theorem phiMap_add (x y : mixedSpace K) : phiMap σ cj (x + y) = phiMap σ cj x + phiMap σ cj y := by
  funext i
  by_cases h : cj i <;> simp [phiMap, h]

theorem phiMap_mp [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (phiMap σ cj) volume volume := by
  have hu : (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1 := by
    first
    | (rw [volume_pi, Measure.pi_of_empty]; simp)
  have h1 : MeasurePreserving (Prod.snd : mixedSpace K → ({w : InfinitePlace K // w.IsComplex} → ℂ))
      volume volume := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.volume_eq_prod, Measure.map_snd_prod]
    first
    | rw [hu, one_smul]
  have h2 : MeasurePreserving (fun (y : {w : InfinitePlace K // w.IsComplex} → ℂ) (i : ι) => y (σ i))
      volume volume :=
    MeasurePreserving.symm _
      (measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace K // w.IsComplex} => (volume : Measure ℂ)) σ)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
    have := Complex.conjLIE.measurePreserving
    convert this using 2
    all_goals first | rfl
  have h3 : MeasurePreserving (fun (z : ι → ℂ) (i : ι) => if cj i then starRingEnd ℂ (z i) else z i)
      (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ)) := by
    refine measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
      (f := fun i c => if cj i then starRingEnd ℂ c else c) (fun i => ?_)
    by_cases h : cj i
    · first
      | (simp only [if_pos h]; exact hc)
    · first
      | (simp only [if_neg h]; exact MeasurePreserving.id _)
  first
  | exact h3.comp (h2.comp h1)

end Covol

end Formalism.L2.SG.NGCut.SplitEmbedding
