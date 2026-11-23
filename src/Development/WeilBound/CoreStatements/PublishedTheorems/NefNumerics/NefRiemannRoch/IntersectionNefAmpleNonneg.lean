module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNumberNonnegEffective
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_cons_nef_ample_nonneg :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (N : LB X) (P : Fin d → LB X), IsNef k N → (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F (Fin.cons N P : Fin (d + 1) → LB X) := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  haveI := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hF N P hN _
    haveI : IsProper (strHom k (X := X)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
    have hN' := (isNef_iff hf).1 hN
    have e : (Fin.cons N P : Fin (0 + 1) → LB X) = ![N] := by
      ext i; fin_cases i; rfl
    rw [e]
    refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hp 1 F (by simpa using hF) ![N]
      (fun i => by fin_cases i; exact hN'.1) fun Z hZ hd => hN'.2 Z hZ (by simpa using hd)
  | succ d ih =>
    intro F _ hF N P hN hP
    have hPb : ∀ i, (P i).IsLB := fun i => (hP i).isLB
    set A := P 0
    set Q : Fin d → LB X := Fin.tail P
    have hQ : ∀ i, IsAmpleLB (Q i) := fun i => hP _
    have hQb : ∀ i, (Q i).IsLB := fun i => (hQ i).isLB
    have hPe : P = Fin.cons A Q := (Fin.cons_self_tail P).symm
    have hL : ∀ i, (Fin.cons N P : Fin (d + 2) → LB X) i |>.IsLB := isLB_cons hN.isLB hPb
    have hsw : (Fin.cons N P : Fin (d + 2) → LB X) ∘ Equiv.swap 0 1 =
        (Fin.cons A (Fin.cons N Q) : Fin (d + 2) → LB X) := by
      rw [hPe]; ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun l => ?_) j
        · rfl
        · have h1 : l.succ.succ ≠ (1 : Fin (d + 2)) := by
            rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_injective _).ne (Fin.succ_ne_zero l)
          rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) h1]
          rfl
    rw [← interNum_comp_perm k F hL (Equiv.swap 0 1), hsw]
    have hfin := finiteCohTwists_of_isProjOver hf F hp
    have hv := diffVanish_chiPic_of_isProjOver hf F hp hF
    obtain ⟨a, ha, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hLa := isLB_lbPow (hP 0).isLB a
    have hNQ : ∀ i, (Fin.cons N Q : Fin (d + 1) → LB X) i |>.IsLB := isLB_cons hN.isLB hQb
    have h0 := ih (cut F hLa s) (suppDim_cut_le _ hLa s hF) N Q hN hQ
    rw [← interNum_cons_eq_interNum_cut hLa s hNQ hfin] at h0
    have h := hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons (hP 0).isLB hNQ)
      (0 : Fin (d + 2)) hLa (hP 0).isLB (a : ℤ) (cls_lbZPow (hP 0).isLB a _)
    simp only [Fin.update_cons_zero] at h
    rw [h] at h0
    exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)

end GlobalTheory
