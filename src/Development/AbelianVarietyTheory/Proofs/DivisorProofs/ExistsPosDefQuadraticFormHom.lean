module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadraticStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_add_add_pull_sub {K : Type} [Field K] {A B : AbVar K} (d : Pic B.X.left)
    (hd : CechPic.pull (Hom.hom (-(𝟙 B))).left d = d) (f g : A ⟶ B) :
    CechPic.pull (f + g).hom.left d + CechPic.pull (f - g).hom.left d
      = (2 : ℤ) • CechPic.pull f.hom.left d + (2 : ℤ) • CechPic.pull g.hom.left d := by
  have hl := (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K B d A.X f.hom g.hom g.hom (-1)).2.2.2.2
  have hq := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd g (-1)).2
  rw [zpow_neg_one] at hl
  rw [neg_one_zsmul] at hq
  norm_num at hq
  have e1 : CechPic.pull (f + g).hom.left d
      = lam d f.hom g.hom + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [lam, add_hom]; abel
  have e2 : CechPic.pull (f - g).hom.left d
      = lam d f.hom (g.hom⁻¹) + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [sub_eq_add_neg, ← hq, lam, add_hom, neg_hom]; abel
  rw [e1, e2, hl]
  simp only [neg_one_smul, two_smul]
  abel

theorem exists_posDef_quadratic_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ,
    (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  intro K _ A B
  obtain ⟨d, hdA, hd⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨c, hc⟩ := GlobalTheory.AV.exists_isAmpleCls K A
  rcases hA : A.dim with _ | n
  · refine ⟨fun _ => 0, fun _ _ => by simp, fun _ => le_rfl, fun f _ => GlobalTheory.T.eq_zero_of_dim_eq_zero' K A B (Or.inl hA) f⟩
  · obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hA])
    refine ⟨fun f => inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left), ?_, ?_, ?_⟩
    · intro f g
      simp only [← hM]
      rw [← MultilinearMap.cons_add, pull_add_add_pull_sub d hd f g, MultilinearMap.cons_add,
        MultilinearMap.cons_smul, MultilinearMap.cons_smul]
      simp [two_mul]
    · intro f
      by_cases hf : f = 0
      · subst hf
        have h0 := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd (0 : A ⟶ B) 0).2
        rw [zero_smul] at h0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul] at h0
        show 0 ≤ inter A _
        rw [← hM, h0, M.map_coord_zero (0 : Fin (n + 1)) (by simp)]
      · exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).le
    · intro f hf0
      by_contra hf
      exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).ne' hf0

end GlobalTheory.AV.AbVar
