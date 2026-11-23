module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFock

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem sch_sharp {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam - root a b) W)
    (hc : ∀ v ∈ W, casimir E v = (casVal lam : ℂ) • v) : False := by
  classical
  have hne : a ≠ b := hab.ne
  have hΛ : lowK ε (lam - root a b) = lowK ε lam - root a b := by
    unfold lowK; abel
  have hW' : IsKIrrHW ε E (lowK ε (lam - root a b)) W := by rw [hΛ]; exact hW
  have hmono' := ssh_strictAnti hmono hh h2 hE a b hW'
  obtain ⟨z, hzW, -, hz0, hzK⟩ := lowFock_exists ε hE hmono' hW'
  have hzK' : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - root a b - rhoC ε) + rhoHol ε) z := hzK
  have hcas : casimir (eT E) z = ((casVal lam : ℝ) : ℂ) • z := by
    obtain ⟨z0, hz0eq⟩ := LinearMap.mem_range.mp hzW
    rw [ssh_casimir_eT, ← hz0eq]
    clear hz0eq
    induction z0 using TensorProduct.induction_on with
    | zero => simp
    | tmul m f => simp [TensorProduct.map_tmul, hc _ m.2, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  have hD2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hzK' hcas
  have hval : nsq (lam - root a b - rhoC ε + rhoC ε) - nsq (rho n) - casVal lam = 2 - 2 * (lam a - lam b) := by
    rw [sub_add_cancel, ssh_nsq_sub_root lam hne]
    unfold casVal
    ring
  have hgap : h ≤ lam a - lam b := by
    have := hh a b hε
    rwa [abs_of_pos (sub_pos.mpr (hmono hab))] at this
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDdef
  have key : tform z ((2 : ℂ) • (D * D) z) = ((2 - 2 * (lam a - lam b) : ℝ) : ℂ) * tform z z := by
    rw [hD2, tform_smul_right, ← hval]
    push_cast
    ring
  rw [tform_smul_right, Module.End.mul_apply, ← tform_D hU] at key
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
  have p1 := tform_self_re_nonneg (D z)
  have p2 := tform_self_re_pos hz0
  have hneg : (2 - 2 * (lam a - lam b)) < 0 := by linarith
  nlinarith

end ReciprocityTheory.ChartRestriction.DS
