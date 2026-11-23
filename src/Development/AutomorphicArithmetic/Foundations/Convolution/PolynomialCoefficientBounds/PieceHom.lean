module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.piece_hom :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (k : ℕ), (piece k f).IsHomogeneous k := by
  intro ι _ f k
  have hlin : ∀ v : ι → ℝ, (lin v).IsHomogeneous 1 := fun v =>
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_C ι ((v i : ℝ) : ℂ)).mul (isHomogeneous_X ℂ i)
  unfold piece Finsupp.sum
  refine IsHomogeneous.sum _ _ _ fun v _ => IsHomogeneous.sum _ _ _ fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have h := (homogeneousComponent_isHomogeneous (k - b) (f.coeff v)).mul
    ((isHomogeneous_C ι ((b.factorial : ℂ)⁻¹)).mul ((hlin v).pow b))
  have e : k - b + (0 + 1 * b) = k := by omega
  rwa [e] at h
