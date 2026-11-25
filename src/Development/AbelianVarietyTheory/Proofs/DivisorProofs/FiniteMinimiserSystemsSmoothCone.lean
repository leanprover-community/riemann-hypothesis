module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.MinSys

open Matrix

theorem finite_of_pos {r : ℕ} (G : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  classical
  set S : Matrix (Fin r) (Fin r) ℤ := LinearMap.BilinForm.toMatrix' G with hS
  have hGS : ∀ x, G x x = x ⬝ᵥ S *ᵥ x := fun x => by
    rw [← Matrix.toBilin'_apply', hS, Matrix.toBilin'_toMatrix']
  have hdet : S.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, hSz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    have h1 := hp z hz
    rw [hGS, hSz, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  have hpsd : (S.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.Poinc.QWDom.gram_posSemidef G hs hn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [hS, LinearMap.BilinForm.toMatrix'_apply]
  have hpd : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
    exact_mod_cast hdet
  obtain ⟨c, hc, hP⟩ := GlobalTheory.Poinc.QWDom.exists_pos_posSemidef_sub_smul_one hpd
  have key : ∀ x : Fin r → ℤ, c * ∑ u, ((x u : ℝ)) ^ 2 ≤ (G x x : ℝ) := by
    intro x
    have h := hP.dotProduct_mulVec_nonneg (fun u => (x u : ℝ))
    simp only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] at h
    have e1 : (fun u => (x u : ℝ)) ⬝ᵥ (S.map (Int.cast : ℤ → ℝ)) *ᵥ (fun u => (x u : ℝ)) = ((x ⬝ᵥ S *ᵥ x : ℤ) : ℝ) := by
      simp [dotProduct, mulVec, Matrix.map_apply]
    have e2 : (fun u => (x u : ℝ)) ⬝ᵥ (c • (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ (fun u => (x u : ℝ)) =
        c * ∑ u, ((x u : ℝ)) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.one_apply, Finset.mul_sum, sq]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2] at h
    rw [hGS]
    exact h
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (B : ℝ) / c ≤ M := exists_nat_ge _
  rw [div_le_iff₀ hc] at hM
  refine (Set.Finite.pi' (fun _ : Fin r => Set.finite_Icc (-(M : ℤ)) M)).subset fun x hx => ?_
  intro u
  have hxB : (G x x : ℝ) ≤ B := by exact_mod_cast hx
  have h1 : ((x u : ℝ)) ^ 2 ≤ ∑ v, ((x v : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun v => ((x v : ℝ)) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ u)
  have h2 : c * ((x u : ℝ)) ^ 2 ≤ c * M := by
    have := (mul_le_mul_of_nonneg_left h1 hc.le).trans ((key x).trans hxB)
    linarith
  have h3 : ((x u : ℝ)) ^ 2 ≤ M := le_of_mul_le_mul_left h2 hc
  have h4 : (x u) ^ 2 ≤ (M : ℤ) := by exact_mod_cast h3
  have h5 := Int.le_self_sq (x u)
  have h6 := Int.le_self_sq (-(x u))
  rw [neg_sq] at h6
  exact ⟨by linarith, by linarith⟩

end GlobalTheory.Poinc.MinSys
