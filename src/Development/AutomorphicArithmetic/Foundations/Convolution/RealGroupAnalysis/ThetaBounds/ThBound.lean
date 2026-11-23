module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CommonMajorant
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Iwa
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical Pointwise

theorem UpperTheory.ConvolutionTheory.R2.Ff.thBound :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), ThBound W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ C hC
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨B₁, N, hB₁⟩ := UpperTheory.ConvolutionTheory.R2.Ff.thMaj F E D W φ hφ c hc
  have hKc : IsCompact (KK F) := (UpperTheory.ConvolutionTheory.R2.Ff.iwa F).1
  have hC' : IsCompact ((gl (F := F) '' KK F) * C) := (hKc.image continuous_gl).mul hC
  obtain ⟨B₂, hB₂⟩ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).2 _ hC' c hc 2
  refine ⟨B₂ * B₁, N, fun y hy g x hx => ?_⟩
  obtain ⟨γ, b, a, k, hk, hg, ha⟩ := hred g
  have hp : 0 < ab a := ab_pos a
  have e1 : f.1 (gl g * x) = f.1 (gl (nU b * mD a) * (gl k * x)) := by
    rw [← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, (π.cusp _ hf).1.left]
  have e2 : Th (W.Om g (W.L (infGL E 2 y) φ)).1 = Th (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ)).1 := by
    rw [← hg]
    exact ((UpperTheory.ConvolutionTheory.R2.Ff.thMeas F E D W (W.L (infGL E 2 y) φ)).2.1 γ g).symm
  have h1 := hB₂ b a (gl k * x) (Set.mul_mem_mul ⟨k, hk, rfl⟩ hx) ha
  have h2 := hB₁ y hy b a k hk ha
  rw [e1, e2, norm_mul]
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ 2) * (B₁ * Ht y ^ N * ab a ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = B₂ * B₁ * Ht y ^ N := by
        field_simp
