module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorOneComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorGeneralPointBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  rw [ringKrullDim_quotient] at h₁ h₂ ⊢
  rw [Order.krullDim_lt_coe_iff] at h₁ h₂ ⊢
  intro l
  have hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_inf]
    exact l.head.2
  have hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun I hI i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))
  rcases hhead with h | h
  · exact h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }
  · exact h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }

theorem proof (hOne : DivisorOneComponent.Statement) (hBr : DivisorBranches.Statement) :
    DivisorGeneralPointBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hOne n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hBr n d J u hJ hdim hu
  refine ⟨I₁ ⊓ I₂, le_inf hle₁ hle₂, quotient_inf_dim_lt hdim₁ hdim₂, ?_⟩
  intro q hqJ hqu hqI
  have hq₁ : q ∉ zeroSet I₁ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).1
  have hq₂ : q ∉ zeroSet I₂ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).2
  obtain ⟨W, hW, hqW, huniq, hnear⟩ := hI₁ q hqJ hqu hq₁
  obtain ⟨m, γ, ord, π, hcov, ⟨N, hN, hsl⟩, hpair, hord, hbij⟩ := hI₂ q hqJ hqu hq₂
  refine ⟨W, hW, hqW, huniq, hnear, m, γ, ord, π, hcov, ⟨N, hN, fun b x hx => ?_⟩, hpair, hord, hbij⟩
  have hKW : J ⊔ Ideal.span {linForm u} ≤ W := hW.1.2
  refine hsl x ⟨fun f hf => hx.1 f (hKW (Ideal.mem_sup_left hf)), hx.2⟩ ?_ b
  have hx0 := hx.1 _ (hKW (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using hx0

end DivisorGeneralPointBranches

end

end GroundTheory.Heights₂.Heights
