module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

end

end GroundTheory.Heights₂.Heights
