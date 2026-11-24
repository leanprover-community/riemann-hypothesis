module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

@[expose] public section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_smul_inv_of_mul_tendsto_invertible (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ) (hL : L.det ≠ 0)
    (hAU : Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L))
    (hdU : Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0)) :
    Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  have hdet : Tendsto (fun τ => (A τ * U τ).det) atImInfty (𝓝 L.det) :=
    ((continuous_id.matrix_det).tendsto L).comp hAU
  have hev : ∀ᶠ τ in atImInfty, (A τ * U τ).det ≠ 0 := hdet.eventually_ne hL

  have hinvdet : Tendsto (fun τ => Ring.inverse (A τ * U τ).det) atImInfty (𝓝 (Ring.inverse L.det)) := by
    simp only [Ring.inverse_eq_inv']
    exact hdet.inv₀ hL
  have hadj : Tendsto (fun τ => (A τ * U τ).adjugate) atImInfty (𝓝 L.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto L).comp hAU
  have hinv : Tendsto (fun τ => (A τ * U τ)⁻¹) atImInfty (𝓝 L⁻¹) := by
    simp only [Matrix.inv_def]
    exact hinvdet.smul hadj
  have hlim : Tendsto (fun τ => (d τ • U τ) * (A τ * U τ)⁻¹) atImInfty (𝓝 0) := by
    have := hdU.mul hinv
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  have hu : IsUnit (A τ * U τ).det := isUnit_iff_ne_zero.mpr hτ
  have h1 : A τ * (U τ * (A τ * U τ)⁻¹) = 1 := by
    rw [← mul_assoc]; exact Matrix.mul_nonsing_inv _ hu
  rw [Matrix.inv_eq_right_inv h1, Matrix.smul_mul]

end GlobalTheory.OddFrame
