module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.AnalyticTorusPointBaseEqHolUnifEx
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.GtKer

theorem ker_iota_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), (∀ z, (Λ.ex0 z).IsZero ↔ ∃ la : Λ.A.La, la.y = 0 ∧ z = Λ.A.P0 la) ∧ (∀ la : Λ.A.La, Out.GtPtF.IsIota (Λ.ε la.y) (Λ.ex0 (Λ.A.P0 la))) ∧ (∀ lam : Λ.A.X →+ ℂ, IsTorusPt (Λ.ex0 (lam, 0)) (fun x => eTwoPi (lam (Λ.ε.symm x)))) ∧ ∀ z x, IsTorusPt (Λ.ex0 z) x → z.2 ∈ Λ.A.abelian₂ := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  refine ⟨GtAnModel.isZero_iff Λ, GtAnModel.isIota Λ, fun lam => ⟨?_, fun x j hc hj => ?_⟩, fun z x h => ?_⟩
  · rw [GtAnModel.analyticTorusPoint_base_eq_holUnif_ex, GtAnModel.ex_zero]
  · obtain ⟨x, rfl⟩ := Λ.ε.surjective x
    have hz := GtAnModel.isLift_gt Λ (lam, 0) x
    have h := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 (lam, 0)).isGen _) hz (j := j) hj
    have h1 := Λ.arcDict_expZero_section (lam, 0) x
    have e : ∀ k k', ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] k = ![Λ.A.ct x + 0, Λ.A.ct x, 0, 0] k' →
        j k = j k' := fun k k' hk =>
      hc k k' (((Category.id_comp _).symm.trans (hz k)).trans
        ((congrArg (fun w => (Λ.u.ex w).left) hk).trans ((Category.id_comp _).symm.trans (hz k')).symm))
    have e₁ : j 0 = j 1 := e 0 1 (by simp)
    have e₂ : j 2 = j 3 := e 2 3 (by simp)
    have n₁ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 1)
    have n₃ := Λ.u.fr_ne _ _ ((hz.le_iff j).1 hj 3)
    have hf : FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct x + (0 : Fin Λ.A.gB → ℂ), Λ.A.ct x, 0, 0] j = 1 := by
      simp only [Matrix.cons_val] at n₁ n₃
      simp only [FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.gtε, Matrix.cons_val, e₁, e₂, add_zero,
        zpow_neg, zpow_one]
      field_simp
    refine h.trans ((congrArg₂ (· * ·) h1 hf).trans ?_)
    simp
  · have h0 : Λ.u.ex z.2 = 1 := Over.OverMorphism.ext ((Λ.ex0_b z).symm.trans ((congrArg (·.left) h.1).trans
      ((toUnit_TF_comp_left _).trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp]))))
    exact Λ.lam.le ((Λ.u.ker _).1 h0)

end GlobalTheory.ArcPts.GtKer
