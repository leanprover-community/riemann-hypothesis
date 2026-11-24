module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem mono_term {n : ℕ} (l : Fin n → ℤ) (w : Fin n → ℂˣ) (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    monomialChar (fun i => -l (Fin.rev i)) (w ∘ Fin.revPerm) =
      (starRingEnd ℂ) (monomialChar l w) := by
  show ∏ i, (((w (Fin.revPerm i)) ^ (-l (Fin.rev i)) : ℂˣ) : ℂ) =
    (starRingEnd ℂ) (∏ i, ((w i ^ l i : ℂˣ) : ℂ))
  rw [map_prod, ← Equiv.prod_comp Fin.revPerm (fun k => (starRingEnd ℂ) ((w k ^ l k : ℂˣ) : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
  rw [← Complex.inv_eq_conj (hw _), zpow_neg, inv_zpow]

private theorem pair_term {n : ℕ} (t : ℝ) (w : Fin n → ℂˣ) (hinj : Function.Injective w)
    (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    ∏ p ∈ prs n, ((w (Fin.rev p.1) : ℂ) - (t : ℂ) * (w (Fin.rev p.2) : ℂ)) /
        ((w (Fin.rev p.1) : ℂ) - (w (Fin.rev p.2) : ℂ)) =
      (starRingEnd ℂ) (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) /
        ((w p.1 : ℂ) - (w p.2 : ℂ))) := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : Fin.rev p.2 ≠ Fin.rev p.1 := fun h => (ne_of_lt hp) (Fin.rev_injective h).symm
    have hab : (w (Fin.rev p.2) : ℂ) ≠ (w (Fin.rev p.1) : ℂ) :=
      fun h => hne (hinj (Units.val_injective h))
    have ha : (w (Fin.rev p.2) : ℂ) ≠ 0 := Units.ne_zero _
    have hb : (w (Fin.rev p.1) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal]
    rw [← Complex.inv_eq_conj (hw _), ← Complex.inv_eq_conj (hw _)]
    generalize (w (Fin.rev p.2) : ℂ) = a at *
    generalize (w (Fin.rev p.1) : ℂ) = b at *
    have h1 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have h2 : a⁻¹ - b⁻¹ ≠ 0 := by
      rw [inv_sub_inv ha hb]
      exact div_ne_zero h1 (mul_ne_zero ha hb)
    rw [div_eq_div_iff h1 h2]
    field_simp

theorem UpperTheory.Gal.Gen.rConj_pf :
    UpperTheory.Gal.Gen.RFormula → UpperTheory.Gal.Gen.RConj := by
  intro hR n t l z hinj hz

  rw [hR n t _ z hinj, hR n t l z hinj, map_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ ?_).symm
  intro σ
  have hw : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hz _
  have hi : Function.Injective (z ∘ σ) := hinj.comp σ.injective
  have h1 := mono_term l (z ∘ σ) hw
  have h2 := pair_term t (z ∘ σ) hi hw
  rw [map_mul]
  simp only [Function.comp_apply] at h2
  rw [← h1, ← h2]
  rfl
