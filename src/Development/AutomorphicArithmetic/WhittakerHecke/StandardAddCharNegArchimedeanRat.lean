module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.standardAddChar_neg_archimedean_rat :
    ∀ x : ℝ, ψ (-(TR.sInf ℚ fun _ => x)) = Complex.exp (2 * Real.pi * Complex.I * x) := by
  intro x
  have hu : Nonempty (InfinitePlace ℚ) := inferInstance
  obtain ⟨w⟩ := hu
  have huniq : ∀ v : InfinitePlace ℚ, v = w := fun v => Subsingleton.elim v w
  have hreal : InfinitePlace.IsReal w := IsTotallyReal.isReal w
  have h : adelicChar ℚ (TR.sInf ℚ fun _ => x) = Real.fourierChar (-x) := by
    have e : TR.sInf ℚ (fun _ => x) = infiniteAdeleInl (TR.infEq ℚ fun _ => x) := rfl
    rw [e, adelicChar_infiniteAdeleInl, Fintype.prod_eq_single w (fun v hv => absurd (huniq v) hv)]
    rw [infiniteAdelicChar_apply_of_isReal hreal]
    have e2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal (TR.infEq ℚ (fun _ => x) w) = x :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply x
    rw [e2]
  have h2 : adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) = Real.fourierChar x := by
    rw [AddChar.map_neg_eq_inv, h, AddChar.map_neg_eq_inv, inv_inv]
  have h3 : ψ (-(TR.sInf ℚ fun _ => x)) = ((adelicChar ℚ (-(TR.sInf ℚ fun _ => x)) : Circle) : ℂ) := rfl
  rw [h3, h2, Real.fourierChar_apply]
  congr 1
  push_cast
  ring
