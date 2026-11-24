module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Summand
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
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

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq GlobalTheory.CuspRep

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)}

def dat2 (b b' : BW.Blo S 2) : BW.Dat S (2 + 2) := BW.Dat.cons b (BW.Dat.cons b' BW.Dat.nil : BW.Dat S (2 + 0))

def ell (b b' : BW.Blo S 2) (k : G1 E (2 + 2)) (f : G1 E (2 + 2) → ℂ) : ℂ :=
  ∫ m₁, ∫ m₂, f (lv (Quotient.out m₁) (Quotient.out m₂) 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GA E 2)) * starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GA E 2))
    ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) ∂quotientMeasure (Gam E 2) (BW.mu1 E 2)

structure BloIn (b : BW.Blo S 2) (τ : Submodule ℂ (L2 (BW.mu1 E 2))) (m : (E →+* ℂ) → Multiset ℂ) (B : Pl E → Multiset ℂ) : Prop where
  mem : ∃ v ∈ τ, Reps (BW.mu1 E 2) v fun g => b.f.1 (g : GA E 2)
  inf : ∀ σ, (Finset.univ.val.map fun i => b.Λ σ i) = m σ
  sat : ∀ w ∉ S, ((b.sat w).map fun x : ℂˣ => (x : ℂ)) = B w

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
