module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem chernPart_null_of_chart_null : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : GlobalTheory.Weight q σ B)
    (ε : ℤˣ) (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) → φ.chernPart D ε Z = 0 := by
  intro k _ X q σ D B φ ε Z hZ hc
  have hchart : ∀ (c : GlobalTheory.AlgChart q σ D) (ρ : GlobalTheory.CxPts q σ → ENNReal),
      GlobalTheory.ChartGlue.chartMeas c.e ρ Z = 0 := by
    intro c ρ
    unfold GlobalTheory.ChartGlue.chartMeas
    have hf : AEMeasurable c.e.symm ((volume.restrict c.e.target).withDensity (ρ ∘ c.e.symm)) :=
      (c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [Measure.map_apply_of_aemeasurable hf hZ]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' c.e.open_target.measurableSet, Set.inter_comm]
    exact hc c
  have hle : ∀ ρ : GlobalTheory.AlgChart q σ D → GlobalTheory.CxPts q σ → ENNReal,
      GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ ≤
        (GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ).restrict Zᶜ := by
    intro ρ
    unfold GlobalTheory.ChartGlue.glueMeas
    refine iSup_le fun c => ?_
    have hae : ∀ᵐ y ∂(GlobalTheory.ChartGlue.chartMeas c.e (ρ c)), y ∈ Zᶜ := by
      rw [ae_iff]
      simpa using hchart c (ρ c)
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact Measure.restrict_mono subset_rfl
      (le_iSup (fun c : GlobalTheory.AlgChart q σ D => GlobalTheory.ChartGlue.chartMeas c.e (ρ c)) c)
  have h3 : φ.chernPart D ε Z ≤ (φ.chernPart D ε).restrict Zᶜ Z :=
    Measure.le_iff'.mp (hle fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Z
  rw [Measure.restrict_apply hZ, Set.inter_compl_self, measure_empty] at h3
  exact nonpos_iff_eq_zero.mp h3

end GlobalTheory.CompanionTheory.MixZ
