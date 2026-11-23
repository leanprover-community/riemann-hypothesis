module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rev :
    ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal → Dens → Fub → CoefPer → Rev := by
  rintro hE hC hF hD hB hP E _ _ _ D W M N P ⟨φ, hφ, h, hne⟩
  obtain ⟨ph, hph, h0⟩ : ∃ ph ∈ Fock D.δ, f0 W N ph φ.1 ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hne (hP E D W M N P φ hφ (fun ph hph => ?_) h)
    have h1 := hC E D W M N P ph hph φ hφ (qr D.δ X0) 1
    rw [← hE E D W M N P ph hph φ hφ, hn ph hph] at h1
    have hδ : qr D.δ X0 ≠ 0 := by
      have := D.neg (Rat.castHom ℝ)
      simp only [qr, X0, eq_ratCast, Rat.cast_lt_zero] at this ⊢
      simpa using this.ne
    have e : {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = qr D.δ X0} = {ξ | qr D.δ ξ = qr D.δ X0} :=
      Set.ext fun ξ => ⟨fun h => h.2, fun h => ⟨(show qr D.δ ξ = _ from h) ▸ hδ, h⟩⟩
    rw [e] at h1
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h1
    refine (mul_eq_zero.1 h1.symm).resolve_left ?_
    simp [Measure.real, adeleMeasure_fundamentalSet]
  obtain ⟨π, hπ, f, hf, h2⟩ := hD M _ (hF E D W M N P ph hph φ hφ) h0
  exact ⟨π, hπ, f, hf, ph, hph, φ, hφ, hB E D W M N P ph hph φ hφ π f hf ▸ h2⟩
