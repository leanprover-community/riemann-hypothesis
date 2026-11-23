module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteOpNorm

theorem span_colP {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : (A * mat x τ).det ≠ 0) (w : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, w = ∑ a, K a • Matrix.mulVec A (X.colP x τ a) := by
  classical
  set M := A * mat x τ with hM
  set c := M⁻¹.mulVec w with hc
  have hw : w = M.mulVec c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  refine ⟨fun a => c (Fin.castLE X.p0_le a), ?_⟩
  have hsum : ∀ f : Fin r → Fin r → ℂ,
      ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ j : Fin r, f j := by
    intro f
    exact Fintype.sum_equiv (finCongr hp) _ _ (fun a => by congr 1)
  show w = ∑ a : Fin X.p0, (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j)) (Fin.castLE X.p0_le a)
  rw [hsum (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j))]
  conv_lhs => rw [hw]
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ReciprocityTheory.ChartRestriction.G.FD.col, hM, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem opNormLe_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, ∀ β : GL (Fin r) E,
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) = herm X.Gm v w) →
    ∀ τ : X.Ψ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x τ (β : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro E _ _ _ r X hp x hx β hβ τ u
  set g : Matrix (Fin r) (Fin r) ℂ := (β : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' : Matrix (Fin r) (Fin r) ℂ := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg : g * g' = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hg'g : g' * g = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hdetg : g.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetx : (mat x τ).det ≠ 0 := (hx τ).1
  have hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v :=
    GlobalTheory.MajInv.hermC_stab X hβ τ.1
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP x τ a := by
    intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · obtain ⟨K, hK⟩ := span_colP X hp x τ 1 (by rw [Matrix.one_mul]; exact hdetx)
        (Matrix.mulVec g (X.colP x τ c))
      exact ⟨K, by simpa only [Matrix.one_mulVec] using hK⟩
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP x τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c) := by
    intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · exact span_colP X hp x τ g (by rw [Matrix.det_mul]; exact mul_ne_zero hdetg hdetx) _
  have key : X.maj x τ (Matrix.mulVec g u) = X.maj x τ u := by
    have h := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer X hx hx τ g g'
      (fun w => by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]) hiso H1 H2 (Matrix.mulVec g u)
    rwa [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec] at h
  rw [key]
  have h0 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ u
  have h1 : (1 : ℝ) ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp (by positivity))
  nlinarith

end GlobalTheory.DefiniteOpNorm
