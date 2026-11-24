module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNearStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartBaseChange
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescendsStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.LogPair.relSnc_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  intro R k _ _ φ X X' f f' π _ _ d s L σ hpb hL hrel
  let W : X.Opens := ⨆ C : SncChart f d L σ, C.U
  have hW : π ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨C', hC'⟩ := hrel.chart y
    obtain ⟨C, hC⟩ := GlobalTheory.T.snc_chart_descends R k φ X X' f f' π d s L σ C' y hpb hC'
    show π y ∈ W
    exact (Opens.mem_iSup).2 ⟨C, hC⟩
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby R k φ X X' f f' π W hpb hW
  refine ⟨a, ha, fun T _ χ hχ Z g ρ hρ => ?_⟩
  have hZ := h T χ hχ Z g ρ hρ
  refine ⟨fun i => LB.isLB_pull (hL i) ρ, fun z => ?_⟩
  have hz : ρ z ∈ W := by
    have : z ∈ ρ ⁻¹ᵁ W := by rw [hZ]; trivial
    exact this
  obtain ⟨C, hC⟩ := (Opens.mem_iSup).1 hz
  obtain ⟨C', hC'⟩ := GlobalTheory.T.snc_chart_base_change R T χ X Z f g ρ d s L σ C hρ
  refine ⟨C', ?_⟩
  rw [hC']
  exact hC
