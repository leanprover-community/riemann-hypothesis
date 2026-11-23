module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def hermPair {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ ((A.map fun x : ℝ => (x : ℂ)) *ᵥ w)).re

def covolume {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) {k : ℕ}
    (v : Fin k → ι → ℂ) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun j l => hermPair Y⁻¹ (v j) (v l)))

def logDetGram {g rk : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin rk) ℂ) : ℝ :=
  Real.log (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).det.re

def unitPolydisc (n : ℕ) : Set (Fin n → ℂ) := {z | ∀ j, ‖z j‖ < 1}

def cuspCoord {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℂ := z (Fin.castLE h j)

def cuspTime {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.log ‖cuspCoord h z j‖⁻¹

def puncturedChart {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ j, cuspCoord h z j ≠ 0}

def chartRadius {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹

def chartImag {n a g : ℕ} (h : a ≤ n) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ0 z).map Complex.im + ∑ j, cuspTime h z j • B j

structure PeriodChartData where

  n : ℕ

  m : ℕ

  g : ℕ

  a : ℕ

  rk : ℕ
  a_le : a ≤ n
  U : Set (Fin n → ℂ)
  isOpen_U : IsOpen U
  U_subset : U ⊆ unitPolydisc n
  τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  τ0_analytic : ∀ j k, AnalyticOnNhd ℂ (fun z => τ0 z j k) U
  τ0_symm : ∀ z ∈ U, (τ0 z)ᵀ = τ0 z
  B : Fin a → Matrix (Fin g) (Fin g) ℝ

  B_psd : ∀ j, (B j).PosSemidef
  c : ℝ
  c_pos : 0 < c
  Y_ge : ∀ z ∈ puncturedChart a_le U, (chartImag a_le τ0 B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  V : Set (Fin m → ℂ)
  isOpen_V : IsOpen V
  f : (Fin n → ℂ) × (Fin m → ℂ) → Matrix (Fin g) (Fin rk) ℂ
  f_analytic : ∀ j k, AnalyticOnNhd ℂ (fun p => f p j k) (U ×ˢ V)
  f_rank : ∀ p ∈ U ×ˢ V, (f p).rank = rk
  K : Set ((Fin n → ℂ) × (Fin m → ℂ))
  isCompact_K : IsCompact K
  K_subset : K ⊆ U ×ˢ V

namespace PeriodChartData

variable (D : PeriodChartData)

def Y (z : Fin D.n → ℂ) : Matrix (Fin D.g) (Fin D.g) ℝ := chartImag D.a_le D.τ0 D.B z

end PeriodChartData

end

end GroundTheory.Heights₂.Heights
