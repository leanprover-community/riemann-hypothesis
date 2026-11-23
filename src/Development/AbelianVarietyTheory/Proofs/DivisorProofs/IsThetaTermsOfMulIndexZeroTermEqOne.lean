module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isThetaTerms_of_mul_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  intro V₁ _ _ D N₁ X C _ e T v c₀ h hv
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩
  intro mu c z J hJ
  have H := h₅ mu c z J hJ
  rw [ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]
  have e₁ : (lift (𝟙 (TF (R := V₁) (FractionRing V₁))) (g c).b).left ≫
      (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  rw [e₁]
  have e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) =
      GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) *
        GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c)) := by
    simp only [GlobalTheory.UT.cst, map_mul]
    rw [gs_mul _ z ⊤ trivial, mul_comm]
  rw [e₂, _root_.mul_assoc, H]
  simp only [GlobalTheory.UT.cst, _root_.mul_assoc]

end GlobalTheory.Poinc.Sep
