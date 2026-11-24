module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_nat_mul_integral_at_all_finite_places :
    ∀ (E : Type) [Field E] [NumberField E] (θ : E), ∃ d : ℕ, 0 < d ∧ ∀ e : ℕ, d ∣ e → ∀ w : H.P E, Valued.v (H.cp w (rt ((e : E) * θ))) ≤ 1 := by
  intro E _ _ θ
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) θ)).exists_integral_multiple
  have hy' : IsIntegral ℤ ((y : E) * θ) := by
    simpa [zsmul_eq_mul] using hy
  have h1 : IsIntegral ℤ ((y.natAbs : E) * θ) := by
    rcases Int.natAbs_eq y with h | h
    · have hc : ((y.natAbs : E)) = (y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc]
      exact hy'
    · have hc : ((y.natAbs : E)) = -(y : E) := by
        conv_rhs => rw [h]
        simp
      rw [hc, neg_mul]
      exact hy'.neg
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  rintro e ⟨k, rfl⟩ w
  have hint : IsIntegral ℤ (((y.natAbs * k : ℕ) : E) * θ) := by
    have he : (((y.natAbs * k : ℕ) : E) * θ) = (k : E) * ((y.natAbs : E) * θ) := by
      push_cast
      ring
    rw [he]
    have hk : IsIntegral ℤ (k : E) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact hk.mul h1
  have hm := coe_algebraMap_mem_adicCompletionIntegers w (⟨_, hint⟩ : 𝓞 E)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hm
