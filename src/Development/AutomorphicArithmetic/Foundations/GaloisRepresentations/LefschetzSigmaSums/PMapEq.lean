module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory.UPel.HT.MapComp

theorem UpperTheory.Gal.LocalSmoothExtension.mapEq_of :
    MapEq := by
  intro G R _ _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₂
  refine ⟨fun m₁ => ?_, fun m => ?_⟩
  · refine ⟨⟨m₁.φ ≫ m₂.φ, m₁.φ₂ ≫ m₂.φ₂, IsGrpPullback.comp m₁.cart m₂.cart,
      isSquare_comp m₁.sq m₂.sq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
        (lbIso_pull_comp m₂.pol m₁.φ₂ rfl), fun y => ?_⟩, rfl⟩
    · rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
    · rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]
  · have hw : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by
      rw [Category.assoc]; exact m.cart.1.w
    let φ : o₁.A.left ⟶ o₂.A.left := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) hw
    have h₁ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
    have h₂ : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
    obtain ⟨φ₂, hsq⟩ := exists_isSquare h₂
    have h₃ : φ₂ ≫ m₂.φ₂ = m.φ₂ := by
      have := isSquare_comp hsq m₂.sq
      rw [h₁] at this
      exact isSquare_unique this m.sq
    have hc : IsGrpPullback o₁.A o₂.A f φ :=
      IsGrpPullback.cancel m₂.cart (by rw [h₁]; exact m.cart) h₂
    refine ⟨⟨φ, φ₂, hc, hsq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
        (lbIso_pull_comp m₂.pol φ₂ h₃.symm).symm, fun y => ?_⟩, h₁⟩
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.act, Category.assoc, m₂.act, ← Category.assoc, h₁]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, h₂, ← Category.assoc, Over.w]
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.eta, Category.assoc, Category.assoc, m₂.eta]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, ← Category.assoc, Over.w]
        simp

end
