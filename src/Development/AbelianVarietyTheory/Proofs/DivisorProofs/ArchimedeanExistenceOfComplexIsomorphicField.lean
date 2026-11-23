module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFamStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIsoStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem archF_of_arch : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  intro κ hF hA R _ _ _ _ D hP hT F _ _ _ e N ν g r m k hg hm hk β ζ q hq s hs vB bX σ gm hAd k₀ hK
  letI : Algebra (FractionRing R) ℂ := ((e : F →+* ℂ).comp (algebraMap (FractionRing R) F)).toAlgebra
  have he : ∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) ℂ x := fun _ => rfl
  obtain ⟨N', ν', I, hb, hh, hl, heX, hth, hrg, hvE, hfam⟩ := GlobalTheory.T.degenerationValues_transport_fieldIso R D F ℂ e he N ν
  obtain ⟨hform, hlev⟩ := GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies F ℂ e N N' I hb hh hl
  obtain ⟨β', hβ⟩ := hform k β
  obtain ⟨q', hq', hev⟩ := hlev m g hm ζ q hq
  obtain ⟨hBK, hadp⟩ := GlobalTheory.T.abelianKeyValue_adaptedVectors_fieldIso κ hF R D F ℂ e he N ν N' ν' I hh hl heX hth hvE vB
  obtain ⟨gm', hpull, hAd'⟩ := hadp r g bX σ gm hAd
  choose s' hs1 hs2 using fun a => hfam (m ^ 2) (s a)
  have hs' : ∀ a, ∃ f, ν'.FamV (s' a) f ∧ IsEvFam N' m (q' a) f := by
    intro a
    obtain ⟨f, hf, hf2⟩ := hs a
    obtain ⟨f', hf', hff⟩ := hs1 a f hf
    exact ⟨f', hf', hev a f f' hf2 hff⟩
  obtain ⟨ε, hε, H⟩ := hA R D hP hT N' ν' g r m k hg hm hk β' _ q' hq' s' hs' vB _ σ gm' hAd' _ (hBK k₀ hK)
  have h1 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).fst = e (jc ν (s a) (gm j) α).fst := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  have h2 : ∀ a j α, (jc ν' (s' a) (gm' j) (I.e α)).snd = e (jc ν (s a) (gm j) α).snd := by
    intro a j α
    rw [hs2 a _ _ (hpull j) α]
    simp [dualMap]
  refine ⟨ε, hε, fun u hu hu' => ?_⟩
  obtain ⟨hsum, x₀, hg₀, lev₀, ϑ, hϑ, hJ, hκ⟩ := H u hu hu'
  refine ⟨fun a j => ⟨?_, ?_⟩, x₀, hg₀, lev₀, ϑ, fun a j => ?_, ?_, hκ⟩
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).1)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · have := ((I.e.toEquiv.summable_iff.2 (hsum a j).2)).mul_left ‖(e (ν.rg ^ (m ^ 2)))⁻¹‖
    refine this.congr fun α => ?_
    simp only [Function.comp, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ]
    rw [← norm_mul, map_div₀, div_eq_inv_mul, _root_.mul_assoc]
  · rw [hϑ a j, ← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h1, hβ, hrg, map_div₀, map_pow]
  · convert hJ using 3 with a j
    rw [← I.e.toEquiv.tsum_eq]
    refine tsum_congr fun α => ?_
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, hβ, hrg, map_div₀, map_pow]

end GlobalTheory.MBLow
