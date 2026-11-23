module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatrixMajorants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace RankOneBoostIsometries

open MajorantConjugateTransfer FlowMatrixMajorants

variable {r : ℕ} (X : Data E r) (τ : X.Ψ)

noncomputable def rk (p w : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i a => p i * ∑ b, τ.1 (X.Gm a b) * conj (w b)

theorem rk_mulVec (p w v : Fin r → ℂ) :
    Matrix.mulVec (rk X τ p w) v = hermC τ.1 X.Gm v w • p := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rk, Matrix.of_apply, hermC, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

noncomputable def boost (e f : Fin r → ℂ) (m σ : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + (((σ - 1) / m : ℝ) : ℂ) • rk X τ e f + (((σ⁻¹ - 1) / m : ℝ) : ℂ) • rk X τ f e

theorem boost_mulVec (e f : Fin r → ℂ) (m σ : ℝ) (v : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) v =
      v + ((((σ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v f) • e +
        ((((σ⁻¹ - 1) / m : ℝ) : ℂ) * hermC τ.1 X.Gm v e) • f := by
  simp only [boost, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
    smul_smul]

section plane

variable {e f : Fin r → ℂ} {m : ℝ} (hm : 0 < m) (hee : hermC τ.1 X.Gm e e = 0)
  (hff : hermC τ.1 X.Gm f f = 0) (hef : hermC τ.1 X.Gm e f = m) (hfe : hermC τ.1 X.Gm f e = m)

include hm hee hff hef hfe

theorem boost_comp {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    Matrix.mulVec (boost X τ e f m σ) (Matrix.mulVec (boost X τ e f m σ⁻¹) w) = w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, hee, hff, hef, hfe, inv_inv]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem boost_isom {σ : ℝ} (hσ : 0 < σ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (boost X τ e f m σ) u) (Matrix.mulVec (boost X τ e f m σ) v) =
      hermC τ.1 X.Gm u v := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [boost_mulVec, boost_mulVec]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
    ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hee, hff, hef, hfe, map_mul, Complex.conj_ofReal]
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v e, ← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 X.Gm_herm v f]
  push_cast
  field_simp
  ring

end plane

end RankOneBoostIsometries

end ReciprocityTheory.ChartRestriction.G.FD
