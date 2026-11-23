module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtFormalTorsion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis

theorem integral_value_at_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ (x : TFK (R := V) F ⟶ A.A) e (t : SecA A F k) (s : Fam D.toPre F k) (c : F), FromGt U.toUnifPre n x → IsTorsFrame A ρ n x e → U.ExpandsF F k w₀ t s → IntGe D v s 0 → ValAt t x e c → 0 ≤ v c := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk x e t s c hp he hts hs hc
  obtain ⟨p, hy, hx⟩ := hp
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ :=
    GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / (n : ℚ) ^ 2) = 0 := simp [hy, QForm.Q_zero hϖ D hQ]
    rwa [e0] at hv₁
  obtain ⟨w, hw, hwv⟩ := WeightValue.exists_pow k (WeightValue.line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := WeightValue.genV_pow k (WeightValue.line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w) c := hsum k hk w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hg := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ hn p
  refine WeightValue.le_of_sumV (q := 0) hS fun β => ?_
  have h := CoefVal.le_v_coef hw (hs β) (hg β) hw0
  have b0 : QForm.bOf D.toPre Q p.y β = 0 := by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  simpa [b0] using h

end GlobalTheory.OneBasis
end
