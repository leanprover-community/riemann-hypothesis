module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.GlueBlocks

theorem isIntV_det {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {d : ℕ}
    (X : Matrix (Fin d) (Fin d) C) (hX : ∀ a b, IsIntV v (X a b)) : IsIntV v X.det := by
  let A' : Matrix (Fin d) (Fin d) (PTb.intRing v) := Matrix.of fun a b => ⟨X a b, hX a b⟩
  have hA : (PTb.intRing v).subtype.mapMatrix A' = X := by ext a b; rfl
  have : X.det = (PTb.intRing v).subtype A'.det := by
    rw [RingHom.map_det, hA]
  rw [this]
  exact (A'.det).2

theorem glue_mul_glue_inv : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (ι : Type) (lab : Fin d → ι)
    (S : ι → Finset (Fin d)) (x y : ι → Matrix (Fin d) (Fin d) C),
    (∀ i a, a ∈ S i → lab a = i) →
    (∀ i a b, x i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) → (∀ i a b, y i a b ≠ 0 → a ∈ S i ∧ b ∈ S i) →
    (∀ i a b, IsIntV v (x i a b)) → (∀ i a b, IsIntV v (y i a b)) →
    (∀ i a c, a ∈ S i → c ∈ S i → ∑ b, x i a b * y i b c = if a = c then 1 else 0) →
    (∀ a b, IsIntV v (glue lab S x a b)) ∧ glue lab S x * glue lab S y = 1 ∧
      v (glue lab S x).det = 0 := by
  intro C _ v d ι lab S x y hlab hx hy hxi hyi hinv
  have hint : ∀ z : ι → Matrix (Fin d) (Fin d) C, (∀ i a b, IsIntV v (z i a b)) →
      ∀ a b, IsIntV v (glue lab S z a b) := by
    intro z hz a b
    simp only [glue, Matrix.of_apply]
    split_ifs
    · exact hz _ _ _
    · unfold IsIntV; rw [v.map_one]
    · unfold IsIntV; rw [v.map_zero]; exact le_top
  have hmul : glue lab S x * glue lab S y = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    by_cases ha : a ∈ S (lab a)
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c = x (lab a) a b * y (lab a) b c := by
        intro b
        simp only [glue, Matrix.of_apply, if_pos ha]
        by_cases hxb : x (lab a) a b = 0
        · rw [hxb, zero_mul, zero_mul]
        · have hb := (hx _ _ _ hxb).2
          have hl : lab b = lab a := hlab _ _ hb
          rw [if_pos (hl ▸ hb), hl]
      simp_rw [hterm]
      by_cases hc : c ∈ S (lab a)
      · exact hinv _ _ _ ha hc
      · have h0 : ∀ b, y (lab a) b c = 0 := by
          intro b; by_contra hne; exact hc (hy _ _ _ hne).2
        simp only [h0, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl; exact hc ha
    · have hterm : ∀ b, glue lab S x a b * glue lab S y b c =
          if a = b then glue lab S y b c else 0 := by
        intro b
        simp only [glue, Matrix.of_apply, if_neg ha]
        split_ifs <;> simp
      simp_rw [hterm]
      rw [Finset.sum_ite_eq Finset.univ a (fun b => glue lab S y b c), if_pos (Finset.mem_univ _)]
      simp only [glue, Matrix.of_apply, if_neg ha]
  refine ⟨hint x hxi, hmul, ?_⟩
  have hd : (glue lab S x).det * (glue lab S y).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have h1 : v (glue lab S x).det + v (glue lab S y).det = 0 := by
    rw [← v.map_mul, hd, v.map_one]
  have hX : (0 : WithTop ℝ) ≤ v (glue lab S x).det := isIntV_det v _ (hint x hxi)
  have hY : (0 : WithTop ℝ) ≤ v (glue lab S y).det := isIntV_det v _ (hint y hyi)
  exact ((add_eq_zero_iff_of_nonneg hX hY).1 h1).1

end GlobalTheory.GlueBlocks
