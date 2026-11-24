module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem fam_ev_param {S : Scheme.{0}} {A T Y : Over S} [GrpObj A] {N : LB (A ⊗ T).left} (hN : Fam A N)
    (y : Y ⟶ T) : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev hN.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)

theorem classify_mono : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left)
    (M : LB (A ⊗ U).left), Rep A b P → Fam A M → Inj A M →
    ∃ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' ∧ Same A M P (fst U S') φ ∧ Mono φ.left := by
  intro S A B S' U _ b P M hP hM hI
  obtain ⟨φ, ⟨hb, hN⟩, -⟩ := hP.univ (U ⊗ S') (snd U S') _ (fam_ev_param hM (fst U S'))
  have hS : Same A M P (fst U S') φ := hN
  refine ⟨φ, hb, hS, ?_⟩
  have hm : Mono φ := ⟨fun {Y} a a' e ↦ by
    have e1 : Same A M P (a ≫ fst U S') (a ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a)).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e2 : Same A M P (a' ≫ fst U S') (a' ≫ φ) := by
      rw [same_iff hM.isLB hP.fam.isLB] at hS ⊢
      have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ a')).left) hS
      simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using this
    have e3 : Same A M M (a ≫ fst U S') (a' ≫ fst U S') := by
      rw [same_iff hM.isLB hP.fam.isLB] at e1 e2
      rw [same_iff hM.isLB hM.isLB, e1, e2, e]
    have ef := hI Y _ _ e3
    have es : a ≫ snd U S' = a' ≫ snd U S' := by rw [← hb, reassoc_of% e]
    exact CartesianMonoidalCategory.hom_ext _ _ ef es⟩
  exact Over.mono_left_of_mono φ
