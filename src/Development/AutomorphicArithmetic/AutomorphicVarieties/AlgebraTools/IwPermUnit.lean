module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLenStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleQuad
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem hk_one {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]
    (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) : hk ρ I 1 = 1 :=
  (hkNorm A G M ρ I 1 hI (one_mem _)).2.1

theorem UpperTheory.V.AlgebraTools.permUnit :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)), IsUnit (resCard k : A) → IsUnit (hk ρ (iwC k n C) (pm k n w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w hq
  have hI : HeckePair (iwC k n C) := (heckePairIwC k n C).1
  induction h : invLen w generalizing w with
  | zero =>
    rw [(lenStep n w).2.1 h, map_one, hk_one ρ _ hI]
    exact isUnit_one
  | succ m ih =>
    have hw : w ≠ 1 := by
      rintro rfl
      have h0 : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
        unfold invLen
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro p _ ⟨h1, h2⟩
        exact lt_asymm h1 h2
      omega
    obtain ⟨i, j, hij, hlt⟩ := (lenStep n w).2.2 hw
    have hlen := ((lenStep n w).1 i j hij).2 hlt
    have hlt' : (Equiv.swap i j * w)⁻¹ i < (Equiv.swap i j * w)⁻¹ j := by
      simpa [_root_.mul_inv_rev, Equiv.swap_inv] using hlt
    have hm := permMul k n C A M ρ (Equiv.swap i j * w) i j hij hlt'
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul] at hm
    rw [← hm]
    exact ((simpleQuad k n C A M ρ i j hij).1 hq).mul (ih _ (by omega))
