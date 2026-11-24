module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f → ∀ (v : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)),
        Wo D f (nE D v * h) = ψ (-(v 1)) * Wo D f h := by
  intro E _ _ D f hf v h
  have hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w := fun u w => by
    simp only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]
  let G : (Fin 2 → A ℚ) → ℂ := fun u => f (nE D u * h) * ψ (u 1)
  have hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) =
      f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)
    rw [e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]
  have key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ) :=
    GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper
  have pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v) := by
    intro u
    have e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1) := by
      rw [← Pp.ψ_add]
      congr 1
      simp only [Pi.add_apply]
      ring
    change _ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))
    rw [hadd, mul_assoc, e2]
    ring
  simp only [Wo, pt]
  rw [integral_const_mul]
  exact congrArg _ key
