module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.REAL
open GlobalTheory.SmoothGlob (lieSet)

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.KStable

variable {n : ℕ} {ε : Fin n → Bool}

theorem skew_of_commute {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) :
    Xᴴ = -X := by
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = (Xᴴ * Jm ε) * Jm ε := by rw [Matrix.mul_assoc]
    _ = -(X * (Jm ε * Jm ε)) := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]

theorem exp_mem_Kset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Kset ε := by
  have hs := skew_of_commute hX hc
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hs]
    have hneg : star t • -X = -(t • X) := by simp
    have hcm : Commute (t • X) (-(t • X)) := (Commute.refl _).neg_right
    rw [hneg, ← Matrix.exp_add_of_commute _ _ hcm]
    simp
  · exact ((show Commute X (Jm ε) from hc).smul_left t).exp_left

end GlobalTheory.CompanionTheory.Hypotheses₂.KStable

end
