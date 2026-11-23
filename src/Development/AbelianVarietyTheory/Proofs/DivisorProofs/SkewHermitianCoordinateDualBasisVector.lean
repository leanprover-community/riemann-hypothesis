module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxCoord_boxVec (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r) (_hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1) :
    ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  rintro ⟨τ', ⟨⟨a', b'⟩, hj⟩⟩ ⟨τ, ⟨⟨a, b⟩, hk⟩⟩
  have hjk : ((τ', (⟨(a', b'), hj⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)})) =
      (τ, (⟨(a, b), hk⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)}))) ↔ τ' = τ ∧ a' = a ∧ b' = b := by
    constructor
    · intro h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  simp only [hjk]
  simp only [boxCoord, boxVec, LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe]
  simp only [entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply]
  by_cases hτ : τ' = τ
  swap
  · split_ifs <;> simp_all
  subst hτ
  simp only [true_and, if_true]
  clear hjk
  split_ifs with h1 h1' h3 h3 h3 h3 h3 h3
  all_goals simp only [LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe, entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply, PiLp.proj_apply, boxEnt, if_true]
  all_goals rcases lt_trichotomy a b with h2 | rfl | h2
  all_goals (try simp only [lt_irrefl, if_false])
  all_goals (try simp only [h2, not_lt_of_gt h2, if_true, if_false])
  all_goals clear _hd
  all_goals (split_ifs with e1 e2 <;> (try obtain ⟨rfl, rfl⟩ := h1') <;> (try obtain ⟨rfl, rfl⟩ := e1) <;> (try obtain ⟨rfl, rfl⟩ := e2) <;> (try simp))
  all_goals (try (simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Prod.ext_iff, ne_eq, Prod.mk.injEq] at *; omega))
  all_goals exact absurd ⟨rfl, rfl⟩ h3

end GlobalTheory.CovTop.VolUp.FrameBox
