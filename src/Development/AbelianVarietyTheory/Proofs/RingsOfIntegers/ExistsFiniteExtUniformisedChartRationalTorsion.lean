module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtIntegralChartUniformisedModelStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitivStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExtStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructureStatement
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

@[expose] public section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlacePrep

theorem exists_good_chart_allRat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∀ M : ℕ, 0 < M → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' ∧ AllRat Xo (xOf y') M := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y hfin M hM
  obtain ⟨T₁, i₁, e₁, y₁, C₁, hext₁, hfin₁, hgood₁⟩ := GlobalTheory.T.exists_finiteExt_integralChart_uniformisedModel E H Dw l Xo c hstar T io y hfin
  obtain ⟨L, _, _, hL, hrat⟩ := (GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo T₁.Fr (xOf y₁) M hM).1
  obtain ⟨T₂, i₂, e₂, ψ, φ, he₂, hv₂, hψ, -, hfin₂⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ L
  obtain ⟨⟨y₂, hext₂⟩, hy⟩ := GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive E H Dw l Xo c T₁ T₂ (i₁.comp io) y₁ i₂ e₂ he₂ hv₂
  have hx₂ := (hy y₂ hext₂).1
  obtain ⟨C₂, hgood₂⟩ := GlobalTheory.T.exists_uniformised_chart_after_valuation_ring_ext E H Dw l Xo c hstar T₁ (i₁.comp io) y₁ C₁ hgood₁ T₂ i₂ e₂ y₂ hext₂
  have htr := ((GlobalTheory.T.exists_integralFramedPoint_baseChange_cdvr_transitive E H Dw l Xo c T T₁ io y i₁ e₁ hext₁.1 hext₁.2.1).2 y₁ hext₁).2 T₂ i₂ e₂ y₂ hext₂
  have hrat₂ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo L _ M hM).2 hrat).1 T₂.Fr ψ.toRingHom
  have hi : i₂ = ψ.toRingHom.comp (algebraMap T₁.Fr L) := RingHom.ext fun a => (hψ a).symm
  have hsp : spMap ψ.toRingHom ≫ spMap (algebraMap T₁.Fr L) ≫ xOf y₁ = xOf y₂ := by
    rw [hx₂, hi, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  rw [hsp] at hrat₂
  exact ⟨T₂, i₂.comp i₁, e₂ * e₁, y₂, C₂, htr, hfin₂ hfin₁, hgood₂, hrat₂⟩

end GlobalTheory.PlacePrep
