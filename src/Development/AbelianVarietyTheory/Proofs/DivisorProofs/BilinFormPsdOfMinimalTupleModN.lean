module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) : 0 < W 0 0 := by
  have h := hW.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at h
  have : (0:ℝ) < (W 0 0 : ℝ) := by push_cast at h; linarith
  exact_mod_cast this

theorem qW_add_smul_single {r : ℕ} (W : Matrix (Fin 8) (Fin 8) ℤ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ))
    (μ : Fin 8 → Fin r → ℤ) (x : Fin r → ℤ) (s : ℤ) :
    qW W b (μ + s • (Pi.single 0 x : Fin 8 → Fin r → ℤ)) = qW W b μ +
      s * (∑ u, ∑ v, W u v * (b ((Pi.single 0 x : Fin 8 → Fin r → ℤ) u) (μ v) + b (μ u) ((Pi.single 0 x : Fin 8 → Fin r → ℤ) v)))
      + s ^ 2 * (W 0 0 * b x x) := by
  set e : Fin 8 → Fin r → ℤ := Pi.single 0 x with he
  have h3 : ∑ u, ∑ v, W u v * b (e u) (e v) = W 0 0 * b x x := by
    rw [Fintype.sum_eq_single 0]
    · rw [Fintype.sum_eq_single 0]
      · simp [he]
      · intro v hv; simp [he, Pi.single_apply, hv]
    · intro u hu; simp [he, Pi.single_apply, hu]
  have hpt : ∀ u v, W u v * b ((μ + s • e) u) ((μ + s • e) v) = W u v * b (μ u) (μ v)
      + s * (W u v * (b (e u) (μ v) + b (μ u) (e v))) + s ^ 2 * (W u v * b (e u) (e v)) := by
    intro u v
    simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  unfold qW
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h3]

theorem psd_of_min : ∀ {r N : ℕ}, 0 < N → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : Fin 8 → Fin r → ℤ), (∀ α : Fin 8 → Fin r → ℤ, (∀ u i, ∃ m : ℤ, α u i = μ u i + N * m) → qW W b μ ≤ qW W b α) → ∀ x, 0 ≤ b x x := by
  intro r N hN W hW b μ hmin x
  by_contra hx
  push_neg at hx
  have hW0 := isE8_apply_zero_zero_pos hW
  set e : Fin 8 → Fin r → ℤ := Pi.single 0 x with he
  set B : ℤ := ∑ u, ∑ v, W u v * (b (e u) (μ v) + b (μ u) (e v)) with hB
  set s : ℤ := (N : ℤ) * (|B| + 1) with hs
  have hmin' := hmin (μ + s • e) (by
    intro u i
    refine ⟨(|B| + 1) * e u i, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    ring)
  rw [qW_add_smul_single] at hmin'
  have hD : W 0 0 * b x x ≤ -1 := by nlinarith
  have hN1 : (1:ℤ) ≤ N := by exact_mod_cast hN
  have hBabs : -|B| ≤ B := neg_abs_le B
  have hBabs2 : B ≤ |B| := le_abs_self B
  have hA : 0 ≤ |B| := abs_nonneg B
  have hs1 : |B| + 1 ≤ s := by rw [hs]; nlinarith
  have h1 : s * B ≤ s * |B| := by nlinarith
  have h2 : s ^ 2 * (W 0 0 * b x x) ≤ - s ^ 2 := by nlinarith
  nlinarith

end GlobalTheory.Poinc
