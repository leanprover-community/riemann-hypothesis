module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidRoot

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem pow_comp_hom {Z H : Over S} [GrpObj H] (f : A ⟶ H) [IsMonHom f] (x : Z ⟶ A) (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem additive_of_birigid (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (h₁ : Triv (ev P (1 : A ⟶ A) (𝟙 A))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ A))) :
    IsAdditive P ∧ IsAdditive (swap P) := by
  apply _root_.GlobalTheory.CubeAxes.additive_of_triv_axes <;> assumption

end GlobalTheory.BirigidRoot

theorem GlobalTheory.BirigidRoot.iso_of_lbPow_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ)
    (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB →
    (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB →
    (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) →
    LBIso P₁ P₂ := by
  intro S A _ _ k P₁ P₂ hA hk _ hP₁ h₁ h₂ hP₂ h₁' h₂' e
  obtain ⟨a₁, b₁⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₁ h₁ h₂
  obtain ⟨a₂, b₂⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₂ h₁' h₂'
  obtain ⟨D, _, Q, -, -, q, q'⟩ := GlobalTheory.dualAbelianScheme S A hA
  obtain ⟨x₁, hx₁, ex₁⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₁ a₁ b₁
  obtain ⟨x₂, hx₂, ex₂⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₂ a₂ b₂
  have hk' : k • cls P₁ hP₁ = k • cls P₂ hP₂ := by
    rw [← cls_lbPow hP₁ k (LB.isLB_linComb hP₁ _ _), ← cls_lbPow hP₂ k (LB.isLB_linComb hP₂ _ _)]
    exact (cls_eq_iff _ _).2 e
  have pw : ∀ (y : A ⟶ D) (n : ℕ), evc q.isLB (fst A A) (snd A A ≫ y ^ n) =
      n • evc q.isLB (fst A A) (snd A A ≫ y) := by
    intro y n
    induction n with
    | zero => rw [pow_zero, MonObj.comp_one, zero_smul]; exact evc_one_right q.isLB q.zero _
    | succ n ih =>
      rw [pow_succ, MonObj.comp_mul, (GlobalTheory.BirigidLift.isAdditive_swap_iff q.isLB).1 q'.additive, ih, succ_nsmul]
  have hpow : x₁ ^ k = x₂ ^ k := GlobalTheory.BirigidLift.dual_ext q (by rw [pw, pw, ← ex₁, ← ex₂, hk'])
  have hx : x₁ = x₂ := by
    obtain ⟨hfl, hsu, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
    have c : (((𝟙 A) ^ k) ≫ x₁).left = (((𝟙 A) ^ k) ≫ x₂).left := by
      rw [GlobalTheory.BirigidRoot.pow_comp_hom, GlobalTheory.BirigidRoot.pow_comp_hom, Category.id_comp, Category.id_comp, hpow]
    rw [Over.comp_left, Over.comp_left] at c
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 A) ^ k).left).1 c)
  subst hx
  exact (cls_eq_iff hP₁ hP₂).1 (ex₁.trans ex₂.symm)
