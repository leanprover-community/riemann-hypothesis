module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem sInt_shift_eq_smul {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [CompleteSpace Vp] (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (f g : Mat k r → ℂ) (c₁ : ℂ)
    (hfg : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), f y = c₁ * g y) (ξ : Vp) (x₀ x : Mat k r)
    (hx₀ : x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    sInt μW μN ψ π (fun y => f (x₀⁻¹ * y)) ξ x = c₁ • sInt μW μN ψ π (fun y => g (x₀⁻¹ * y)) ξ x := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hW.2.2.1)
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hN.2.2.1)
  unfold sInt
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hfg _ (mul_mem_UH' (inv_mem_UH' hx₀) (mul_mem_UH' (mul_mem_UH' hp1.1 hp2.1) hx)), mul_smul]

end ReciprocityTheory.ChartRestriction.DS.Lap
