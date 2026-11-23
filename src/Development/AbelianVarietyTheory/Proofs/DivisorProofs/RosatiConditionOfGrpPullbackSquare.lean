module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RosatiPull

theorem sq_left_ext {H : Scheme.{0}} {G : Over H} {Z : Scheme.{0}} {a b : Z ⟶ (G ⊗ G).left}
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext h1 h2

theorem rosatiFor_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  intro p _ D S H E A₀ _ P hP AH _ AE _ f φ φ₂ φ₂H actH actE _ hsq hact hR c
  have hu : (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH ≫ actH.act c) (snd AH AH)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.1, Category.assoc]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
  have hv : (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst AH AH) (snd AH AH ≫ actH.act (D.star c).unop)).left := by
    apply sq_left_ext
    · simp only [Category.assoc, ← Over.comp_left, lift_fst]
      rw [hsq.1]
      simp only [← Category.assoc, ← Over.comp_left, lift_fst]
    · simp only [Category.assoc, ← Over.comp_left, lift_snd]
      rw [hsq.2]
      simp only [← Category.assoc, ← Over.comp_left, lift_snd]
      simp only [Over.comp_left, Category.assoc, hact]
      rw [← Category.assoc φ₂, hsq.2, Category.assoc]
  have hQ : (P.pull φ₂H).IsLB := pull_isLB hP _
  have hR' : (P.pull (φ₂ ≫ φ₂H)).IsLB := pull_isLB hP _
  have e3 := GlobalTheory.GenSpread.lbIso_pull_comp (L := P.pull φ₂H) (M := P.pull φ₂H) φ₂ hu hv (hR c)
  have e1u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE ≫ actE.act c) (snd AE AE)).left (a := φ₂ ≫ φ₂H) rfl
  have e2u := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE ≫ actE.act c) (snd AE AE)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  have e1v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    (lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left (a := φ₂ ≫ φ₂H) rfl
  have e2v := GlobalTheory.GenSpread.lbIso_pull_pull hP
    ((lift (fst AE AE) (snd AE AE ≫ actE.act (D.star c).unop)).left ≫ φ₂) (a := φ₂H) (Category.assoc _ _ _).symm
  exact LBIso.trans (pull_isLB hR' _) (pull_isLB hP _) (pull_isLB hR' _) e1u.symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hQ _) (pull_isLB hR' _) e2u
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB hR' _) e3
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hP _) (pull_isLB hR' _) e2v.symm e1v)))

end GlobalTheory.RosatiPull
