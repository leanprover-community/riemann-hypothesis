module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_values_complex_fibre : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  intro hT E _ _ _ H Dw l Xo y s
  have hsm : Smooth (gxSnd y) := by
    have := Xo.univ.t.semi.smooth
    exact inferInstanceAs (Smooth (pullback.fst y Xo.univ.t.G.hom))
  have hred : IsReduced (Gx y) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ _ (gxSnd y) hsm).1
  have h1 : ∀ (a : ℂ) i (f : Γ(Gx y, (PPx y).U i)) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) (scal y a i * f) = a * valAt' pt ((PPx y).U i) f := fun a i f pt hp => by
    by_cases h : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i
    · rw [valAt'_mul]
      exact congrArg (· * _) (valAt'_constFn pt (gxSnd y) hp _ a h)
    · rw [valAt'_of_not_le pt h, valAt'_of_not_le pt h, mul_zero]
  have h3 : ∀ i (f g : Γ(Gx y, (PPx y).U i)), (∀ pt : Sp ℂ ⟶ Gx y, pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) f = valAt' pt ((PPx y).U i) g) → f = g := fun i f g h =>
    ComplexPoints.eq_of_valAt'_eq (gxSnd y) _ f g fun pt hp _ => h pt hp
  refine ⟨fun a i pt hp => h1 a i _ pt hp, ⟨fun hs => ?_, ?_⟩, fun s' h i => h3 i _ _ (h i)⟩
  · by_contra hne
    have h0 : ∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s.f i) = 0 := fun i pt hp => by
      by_contra h
      exact hne ⟨i, pt, hp, h⟩
    have hall : ∀ (a : ℂ) i, s.f i = scal y a i * s.f i := fun a i => h3 i _ _ fun pt hp => by
      rw [h1 a i _ pt hp, h0 i pt hp, mul_zero]
    exact zero_ne_one ((hs s).unique (hall 0) (hall 1))
  · rintro ⟨j, q, hq, hv⟩ s'
    obtain ⟨s₀, hs₀⟩ := gfp_gen hT y
    obtain ⟨c, hc, -⟩ := hs₀ s
    have hc0 : c ≠ 0 := fun h => hv (by rw [hc j, h1 c j _ q hq, h, zero_mul])
    obtain ⟨b, hb, hu⟩ := hs₀ s'
    refine ⟨b / c, fun i => h3 i _ _ fun pt hp => ?_, fun a ha => ?_⟩
    · rw [h1 _ i _ pt hp, hb i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, ← mul_assoc, div_mul_cancel₀ _ hc0]
    · rw [eq_div_iff hc0]
      refine hu _ fun i => h3 i _ _ fun pt hp => ?_
      rw [h1 _ i _ pt hp, ha i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, mul_assoc]

end GlobalTheory
