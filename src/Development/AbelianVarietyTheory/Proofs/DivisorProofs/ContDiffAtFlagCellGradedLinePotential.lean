module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.CellPotSmooth

theorem upM_fb_contDiffAt_two {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (τ : ι) (w : V n) :
    MContDiffAt 2 (fun w => upM (fb ε w) τ) w := by
  intro a b
  simp only [upM, upU, Matrix.of_apply, fb]
  split_ifs with h1 h2
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (ε.symm (.inr ⟨τ, ⟨(b, a), h1⟩⟩))).contDiff.restrict_scalars ℝ).contDiffAt
  · exact contDiffAt_const
  · exact contDiffAt_const

theorem G_bsL_smooth {ι : Type} {m : ι → ℕ} {n d : ℕ} (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (τ : ι)
    (hG : MContDiffAt 2 (fun v => G v τ) (bsL ε w)) : MContDiffAt 2 (fun w => G (bsL ε w) τ) w := by
  intro a b
  exact (hG a b).comp w (((bsL ε).contDiff.restrict_scalars ℝ).contDiffAt)

theorem upU_isUnit {s : ℕ} (y : Low s → ℂ) : IsUnit (upU y) := by
  rw [Matrix.isUnit_iff_isUnit_det, upU_eq, Matrix.det_transpose, GlobalTheory.FlagFibre.det_uni]
  exact isUnit_one

theorem leadMinor_re_pos {s : ℕ} {A : Matrix (Fin s) (Fin s) ℂ} (hA : A.PosDef) (j : ℕ) : 0 < (leadMinor A j).re := by
  have h := (hA.submatrix (Subtype.val_injective (p := fun a : Fin s => (a : ℕ) < j))).det_pos
  exact (Complex.pos_iff.1 h).1

theorem cellPot_contDiffAt : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  intro ι m n d ε G w x hP hG
  set A : V n → Matrix (Fin (m x.1)) (Fin (m x.1)) ℂ :=
    fun w => upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ with hAdef
  have hA : MContDiffAt 2 A w :=
    ((upM_fb_contDiffAt_two ε x.1 w).mul (G_bsL_smooth ε G w x.1 hG)).mul (upM_fb_contDiffAt_two ε x.1 w).conjTranspose
  have hPA : (A w).PosDef := by
    refine hP.mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2 (upU_isUnit _)
  have hm : ∀ j : ℕ, ContDiffAt ℝ 2 (fun w => (leadMinor (A w) j).re) w := fun j =>
    Complex.reCLM.contDiff.contDiffAt.comp w (hA.submatrix _ _).det
  have h1 := leadMinor_re_pos hPA (x.2 + 1)
  have h0 := leadMinor_re_pos hPA x.2
  have hpos : 0 < grD (A w) x.2 := div_pos h1 h0
  refine ⟨?_, hpos⟩
  have hd : ContDiffAt ℝ 2 (fun w => grD (A w) x.2) w := (hm _).div (hm _) h0.ne'
  exact (hd.log hpos.ne').neg

end GlobalTheory.CellPotSmooth
