module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ArchFourier

theorem fourier_twice_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ d : ℂ, d ≠ 0 ∧ ∀ (f : SInf F κ) (a : κ → mixedEmbedding.mixedSpace F),
      ∫ y, (∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ a) : ℝ)) ∂μ =
      d * f (-a) := by
  intro F _ _ κ _ _ _ μ hμ
  classical
  obtain ⟨⟨c, hc, hinv⟩, hint⟩ := GlobalTheory.fourier_inversion_haar_symm_form (-(traceDot F κ))
    (fun x y => by simp only [LinearMap.neg_apply, traceDot_comm x y])
    (fun x hx => traceDot_nondeg x (fun y => by simpa using hx y)) μ hμ
  refine ⟨(c : ℂ), by exact_mod_cast hc.ne', fun f a => ?_⟩
  have hk : ∀ x y : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (2 * Real.pi * Complex.I * (((-(traceDot F κ)) x y : ℝ) : ℂ)) =
        Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) := by
    intro x y
    rw [LinearMap.neg_apply, LinearMap.neg_apply, traceDot_apply]
    push_cast
    ring_nf
  have h := hinv f f.continuous (hint f).1 (hint f).2 a
  simp only [hk] at h
  exact h

end GlobalTheory.ArchFourier
